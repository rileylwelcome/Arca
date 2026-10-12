/*
 * Arca demo engine
 * -----------------
 * Pure functions over a plain JSON state. No UI, no network, no real money.
 * All amounts are integer cents. All times are epoch milliseconds supplied by
 * the caller (the prototype uses a movable demo clock), so every rule is
 * deterministic and testable.
 *
 * Sections:
 *   1. Money and time helpers
 *   2. State shape and seed data
 *   3. Envelope rules (schedules, commitment mode, cooling-off)
 *   4. Ledger (manual spending, holds, captures, releases, refunds)
 *   5. Restriction logic (card authorization simulation, shield events)
 *   6. Wishlist, forgone purchases, reflections, goal
 *   7. Progress calculations
 *   8. Self-tests
 *
 * Rules that a native build should keep:
 *   - A purchase counts toward the period in which it was authorized (or, for
 *     manual entries, the date the person gives). Captures and refunds adjust
 *     that same period, so a refund never inflates a later period's allowance.
 *   - Approved authorizations are held (reserved) until captured or released.
 *   - Available = budget in force now - completed spending - pending holds.
 *   - Tightening a rule takes effect immediately. Loosening a rule while
 *     commitment mode is on is scheduled after the cooling-off period.
 *   - Declined attempts never create spending or holds.
 *   - Repeated attempts at the same merchant for the same amount within 24
 *     hours are one purchase intent for progress metrics.
 */
(function (root) {
  'use strict';

  var HOUR = 3600000;
  var DAY = 24 * HOUR;
  var STATE_VERSION = 3;
  var INTENT_WINDOW_MS = DAY;
  var MODE_RANK = { reminder: 1, access: 2, payment: 3 };
  var DEFAULT_WISH_COOL_DAYS = 7;

  /* ---------------------------------------------------------------- 1 ---- */

  function clone(o) { return JSON.parse(JSON.stringify(o)); }
  function isCents(n) { return typeof n === 'number' && Number.isSafeInteger(n); }
  function fail(msg) { throw new Error(msg); }
  function nextId(s, prefix) { s.seq = (s.seq || 0) + 1; return prefix + '_' + s.seq; }

  // Parse user text such as "12", "12.5", "$1,204.99" into cents. Returns null
  // for anything that is not a plain non-negative amount with at most 2 decimals.
  function toCents(input) {
    if (input === null || input === undefined) return null;
    var s = String(input).trim().replace(/[$,\s]/g, '');
    var m = /^(\d*)(?:\.(\d{0,2}))?$/.exec(s);
    if (!m || (m[1] === '' && !m[2])) return null;
    var whole = m[1] ? parseInt(m[1], 10) : 0;
    var frac = m[2] ? parseInt((m[2] + '00').slice(0, 2), 10) : 0;
    var c = whole * 100 + frac;
    return Number.isSafeInteger(c) ? c : null;
  }

  function formatCents(c, opt) {
    opt = opt || {};
    if (!isCents(c)) return '—';
    var neg = c < 0; c = Math.abs(c);
    var d = Math.floor(c / 100), r = c % 100;
    var str = '$' + String(d).replace(/\B(?=(\d{3})+(?!\d))/g, ',');
    if (!(opt.short && r === 0)) str += '.' + (r < 10 ? '0' : '') + r;
    return (neg ? '−' : '') + str;
  }

  function startOfDay(t) { var d = new Date(t); return new Date(d.getFullYear(), d.getMonth(), d.getDate()).getTime(); }
  function addDays(t, n) { var d = new Date(t); return new Date(d.getFullYear(), d.getMonth(), d.getDate() + n, d.getHours(), d.getMinutes(), d.getSeconds(), d.getMilliseconds()).getTime(); }

  // Weekly periods start Monday 00:00 local time; monthly periods start on the 1st.
  function periodStart(cadence, t) {
    var d = new Date(t);
    if (cadence === 'monthly') return new Date(d.getFullYear(), d.getMonth(), 1).getTime();
    var back = (d.getDay() + 6) % 7;
    return new Date(d.getFullYear(), d.getMonth(), d.getDate() - back).getTime();
  }
  function periodEnd(cadence, t) {
    var s = new Date(periodStart(cadence, t));
    if (cadence === 'monthly') return new Date(s.getFullYear(), s.getMonth() + 1, 1).getTime();
    return new Date(s.getFullYear(), s.getMonth(), s.getDate() + 7).getTime();
  }

  /* ---------------------------------------------------------------- 2 ---- */

  var DEFAULT_MERCHANTS = [
    { id: 'amazon', name: 'Amazon', domain: 'amazon.com', kind: 'Marketplace' },
    { id: 'target', name: 'Target', domain: 'target.com', kind: 'Retail' },
    { id: 'doordash', name: 'DoorDash', domain: 'doordash.com', kind: 'Food delivery' },
    { id: 'hearth', name: 'Hearth & Loom', domain: 'hearthandloom.shop', kind: 'Home goods', custom: true }
  ];

  function emptyState(startedAt) {
    return {
      version: STATE_VERSION, seq: 0, startedAt: startedAt, clockOffsetMs: 0,
      onboarded: false, profile: { name: '' }, focus: [],
      merchants: clone(DEFAULT_MERCHANTS),
      envelopes: [], cards: [], holds: [], spend: [], refunds: [], attempts: [],
      shieldEvents: [], nudges: [], forgone: [], wishlist: [], reflections: [],
      goal: null, dismissed: {}
    };
  }

  /* ---------------------------------------------------------------- 3 ---- */

  // Each rule is a schedule of {value, effectiveAt, requestedAt}. The value in
  // force at time t is the latest entry with effectiveAt <= t. Entries in the
  // future are pending changes.
  var FIELDS = ['budget', 'mode', 'commitment', 'cooling', 'active'];

  function valueAt(list, t) {
    var best = null;
    for (var i = 0; i < list.length; i++) {
      var e = list[i];
      if (e.effectiveAt <= t && (best === null || e.effectiveAt >= best.effectiveAt)) best = e;
    }
    return best ? best.value : undefined;
  }

  function rulesAt(env, t) {
    return {
      budgetCents: valueAt(env.sched.budget, t) || 0,
      mode: valueAt(env.sched.mode, t) || 'reminder',
      commitment: !!valueAt(env.sched.commitment, t),
      coolingHours: valueAt(env.sched.cooling, t) || 48,
      active: valueAt(env.sched.active, t) === true
    };
  }

  function pendingChanges(env, now) {
    var out = [];
    FIELDS.forEach(function (f) {
      env.sched[f].forEach(function (e) {
        if (e.effectiveAt > now) out.push({ field: f, value: e.value, effectiveAt: e.effectiveAt, requestedAt: e.requestedAt });
      });
    });
    return out.sort(function (a, b) { return a.effectiveAt - b.effectiveAt; });
  }

  function findEnv(s, id) { for (var i = 0; i < s.envelopes.length; i++) if (s.envelopes[i].id === id) return s.envelopes[i]; return null; }
  function findMerchant(s, id) { for (var i = 0; i < s.merchants.length; i++) if (s.merchants[i].id === id) return s.merchants[i]; return null; }
  function findCard(s, id) { for (var i = 0; i < s.cards.length; i++) if (s.cards[i].id === id) return s.cards[i]; return null; }

  function activeEnvelopes(s, now) {
    return s.envelopes.filter(function (e) { return e.createdAt <= now && rulesAt(e, now).active; });
  }

  function addMerchant(state, input) {
    var s = clone(state);
    var name = String(input.name || '').trim();
    if (!name) fail('Give the merchant a name.');
    if (name.length > 40) fail('Keep the merchant name under 40 characters.');
    var m = { id: nextId(s, 'm'), name: name, domain: String(input.domain || '').trim(), kind: input.kind || 'Custom merchant', custom: true };
    s.merchants.push(m);
    return { state: s, result: { merchantId: m.id } };
  }

  function createEnvelope(state, input, now) {
    var s = clone(state);
    if (!findMerchant(s, input.merchantId)) fail('Choose a merchant for this envelope.');
    if (!isCents(input.budgetCents) || input.budgetCents <= 0) fail('Set a budget above $0.');
    if (input.cadence !== 'weekly' && input.cadence !== 'monthly') fail('Choose weekly or monthly.');
    if (!MODE_RANK[input.mode]) fail('Choose how Arca should step in.');
    var dup = activeEnvelopes(s, now).some(function (e) { return e.merchantId === input.merchantId; });
    if (dup) fail('There is already an envelope for this merchant.');
    var at = now;
    var env = {
      id: nextId(s, 'env'), merchantId: input.merchantId, cadence: input.cadence, createdAt: at,
      sched: {
        budget: [{ value: input.budgetCents, effectiveAt: at, requestedAt: at }],
        mode: [{ value: input.mode, effectiveAt: at, requestedAt: at }],
        commitment: [{ value: !!input.commitment, effectiveAt: at, requestedAt: at }],
        cooling: [{ value: input.coolingHours || 48, effectiveAt: at, requestedAt: at }],
        active: [{ value: true, effectiveAt: at, requestedAt: at }]
      }
    };
    s.envelopes.push(env);
    var card = makeCard(s, env, 'reusable', at);
    return { state: s, result: { envelopeId: env.id, cardId: card.id } };
  }

  function isLoosening(field, current, next) {
    if (field === 'budget') return next > current;
    if (field === 'mode') return MODE_RANK[next] < MODE_RANK[current];
    if (field === 'commitment') return current === true && next === false;
    if (field === 'cooling') return next < current;
    if (field === 'active') return current === true && next === false;
    return false;
  }

  // Request a rule change. Returns whether it was delayed and when it applies.
  function requestChange(state, envId, field, value, now) {
    if (FIELDS.indexOf(field) < 0) fail('Unknown setting.');
    var s = clone(state);
    var env = findEnv(s, envId); if (!env) fail('Envelope not found.');
    var r = rulesAt(env, now);
    if (!r.active) fail('This envelope is closed.');
    if (field === 'budget' && (!isCents(value) || value <= 0)) fail('Set a budget above $0.');
    if (field === 'mode' && !MODE_RANK[value]) fail('Choose how Arca should step in.');
    if (field === 'cooling' && [24, 48, 72].indexOf(value) < 0) fail('Cooling-off can be 24, 48 or 72 hours.');
    var current = { budget: r.budgetCents, mode: r.mode, commitment: r.commitment, cooling: r.coolingHours, active: r.active }[field];
    var future = env.sched[field].filter(function (e) { return e.effectiveAt > now; });

    // Asking again for a change that is already scheduled keeps the original timer.
    if (future.length && future[future.length - 1].value === value) {
      return { state: state, result: { field: field, value: value, delayed: true, effectiveAt: future[future.length - 1].effectiveAt, unchanged: true } };
    }
    if (value === current && !future.length) {
      return { state: state, result: { field: field, value: value, delayed: false, effectiveAt: now, unchanged: true } };
    }
    var loosen = isLoosening(field, current, value);
    var delayed = loosen && r.commitment;
    var effectiveAt = delayed ? now + r.coolingHours * HOUR : now;
    // A new request supersedes anything still pending for this setting.
    env.sched[field] = env.sched[field].filter(function (e) { return e.effectiveAt <= now; });
    if (!(value === current && !delayed)) env.sched[field].push({ value: value, effectiveAt: effectiveAt, requestedAt: now });
    return { state: s, result: { field: field, value: value, delayed: delayed, effectiveAt: effectiveAt, cancelledPending: future.length > 0 } };
  }

  // Withdrawing a pending loosening is always allowed immediately.
  function cancelPending(state, envId, field, effectiveAt, now) {
    var s = clone(state);
    var env = findEnv(s, envId); if (!env) fail('Envelope not found.');
    var before = env.sched[field].length;
    env.sched[field] = env.sched[field].filter(function (e) { return !(e.effectiveAt === effectiveAt && e.effectiveAt > now); });
    if (env.sched[field].length === before) fail('That change already took effect or was cancelled.');
    return { state: s, result: { field: field } };
  }

  // Onboarding sets up an envelope's starting rules directly. It is setup, not
  // a change request, so it is not subject to cooling-off.
  function configureEnvelope(state, envId, cfg, now) {
    var s = clone(state);
    var env = findEnv(s, envId); if (!env) fail('Envelope not found.');
    var map = { budget: cfg.budgetCents, mode: cfg.mode, commitment: cfg.commitment, cooling: cfg.coolingHours };
    Object.keys(map).forEach(function (f) {
      if (map[f] === undefined) return;
      env.sched[f] = env.sched[f].filter(function (e) { return e.effectiveAt <= now; });
      env.sched[f].push({ value: map[f], effectiveAt: now, requestedAt: now });
    });
    if (cfg.cadence && cfg.cadence !== env.cadence) env.cadence = cfg.cadence;
    return { state: s, result: { envelopeId: envId } };
  }

  /* ---------------------------------------------------------------- 4 ---- */

  function refundedCents(s, spendId, asOf) {
    var t = 0;
    s.refunds.forEach(function (r) { if (r.spendId === spendId && (asOf === undefined || r.at <= asOf)) t += r.amountCents; });
    return t;
  }

  function completedInWindow(s, envId, from, to, asOf) {
    var total = 0;
    s.spend.forEach(function (x) {
      if (x.envelopeId !== envId || x.occurredAt < from || x.occurredAt >= to) return;
      if (asOf !== undefined && x.postedAt > asOf) return;
      total += x.amountCents - refundedCents(s, x.id, asOf);
    });
    return total;
  }

  function pendingInWindow(s, envId, from, to) {
    var total = 0;
    s.holds.forEach(function (h) {
      if (h.envelopeId === envId && h.status === 'pending' && h.createdAt >= from && h.createdAt < to) total += h.amountCents;
    });
    return total;
  }

  function envelopeSummary(s, envId, now) {
    var env = findEnv(s, envId); if (!env) return null;
    var r = rulesAt(env, now);
    var from = periodStart(env.cadence, now), to = periodEnd(env.cadence, now);
    var completed = completedInWindow(s, envId, from, to, now);
    var pending = pendingInWindow(s, envId, from, to);
    var committed = completed + pending;
    return {
      id: env.id, env: env, merchant: findMerchant(s, env.merchantId), rules: r,
      cadence: env.cadence, periodStart: from, resetsAt: to,
      budgetCents: r.budgetCents, completedCents: completed, pendingCents: pending,
      availableCents: Math.max(0, r.budgetCents - committed),
      overCents: Math.max(0, committed - r.budgetCents),
      pendingChanges: pendingChanges(env, now)
    };
  }

  function addManualSpend(state, input, now) {
    var s = clone(state);
    var env = findEnv(s, input.envelopeId); if (!env) fail('Choose an envelope.');
    if (!isCents(input.amountCents) || input.amountCents <= 0) fail('Enter an amount above $0.');
    var occurredAt = input.occurredAt === undefined ? now : input.occurredAt;
    if (occurredAt > now) fail('Spending can’t be dated in the future.');
    var x = { id: nextId(s, 'sp'), envelopeId: env.id, merchantId: input.merchantId || env.merchantId, amountCents: input.amountCents, occurredAt: occurredAt, postedAt: now, source: 'manual', note: String(input.note || '').slice(0, 80) };
    s.spend.push(x);
    return { state: s, result: { spendId: x.id } };
  }

  // Merchant capture. A capture can differ from the authorization (tips, final
  // weight). The cap is enforced at authorization; captures for approved
  // authorizations are not blocked, which matches how issuing processors work.
  function captureHold(state, holdId, amountCents, now) {
    var s = clone(state);
    var h = null; s.holds.forEach(function (x) { if (x.id === holdId) h = x; });
    if (!h) fail('Hold not found.');
    if (h.status !== 'pending') fail('This hold was already ' + h.status + '.');
    var amt = amountCents === undefined ? h.amountCents : amountCents;
    if (!isCents(amt) || amt <= 0) fail('Enter a capture amount above $0.');
    h.status = 'captured'; h.capturedCents = amt; h.resolvedAt = now;
    var x = { id: nextId(s, 'sp'), envelopeId: h.envelopeId, merchantId: h.merchantId, amountCents: amt, occurredAt: h.createdAt, postedAt: now, source: 'card', holdId: h.id, note: h.note || '' };
    s.spend.push(x);
    return { state: s, result: { spendId: x.id, releasedCents: Math.max(0, h.amountCents - amt), overCaptureCents: Math.max(0, amt - h.amountCents) } };
  }

  // Authorization reversal: the merchant never captures, the reservation ends.
  function releaseHold(state, holdId, now) {
    var s = clone(state);
    var h = null; s.holds.forEach(function (x) { if (x.id === holdId) h = x; });
    if (!h) fail('Hold not found.');
    if (h.status !== 'pending') fail('This hold was already ' + h.status + '.');
    h.status = 'released'; h.resolvedAt = now;
    return { state: s, result: { releasedCents: h.amountCents } };
  }

  function refundSpend(state, spendId, amountCents, now) {
    var s = clone(state);
    var x = null; s.spend.forEach(function (y) { if (y.id === spendId) x = y; });
    if (!x) fail('Purchase not found.');
    var remaining = x.amountCents - refundedCents(s, x.id);
    if (!isCents(amountCents) || amountCents <= 0) fail('Enter a refund above $0.');
    if (amountCents > remaining) fail('Refund can’t be more than ' + formatCents(remaining) + ', the amount not yet refunded.');
    s.refunds.push({ id: nextId(s, 'rf'), spendId: x.id, envelopeId: x.envelopeId, amountCents: amountCents, at: now });
    return { state: s, result: { remainingCents: remaining - amountCents } };
  }

  /* ---------------------------------------------------------------- 5 ---- */

  function makeCard(s, env, type, now) {
    var n = (s.seq + 1);
    var card = { id: nextId(s, 'card'), envelopeId: env.id, merchantId: env.merchantId, type: type, last4: String(4000 + (n * 37) % 6000).slice(-4), status: 'active', createdAt: now };
    s.cards.push(card);
    return card;
  }

  function createCard(state, envId, type, now) {
    if (type !== 'reusable' && type !== 'single_use') fail('Unknown card type.');
    var s = clone(state);
    var env = findEnv(s, envId); if (!env) fail('Envelope not found.');
    if (!rulesAt(env, now).active) fail('This envelope is closed.');
    var card = makeCard(s, env, type, now);
    return { state: s, result: { cardId: card.id } };
  }

  function cardsFor(s, envId) { return s.cards.filter(function (c) { return c.envelopeId === envId; }); }

  // Simulate an issuer authorization decision for a demo card. Mirrors the
  // order a hosted rules engine would apply: card state, merchant lock, cap.
  function decideAuthorization(s, card, merchantId, amountCents, now) {
    var env = findEnv(s, card.envelopeId);
    var r = rulesAt(env, now);
    var sum = envelopeSummary(s, env.id, now);
    if (card.status === 'used') return { decision: 'declined', reason: 'card_used' };
    if (card.status !== 'active') return { decision: 'declined', reason: 'card_inactive' };
    if (!r.active) return { decision: 'declined', reason: 'envelope_closed' };
    if (merchantId !== card.merchantId) return { decision: 'declined', reason: 'wrong_merchant' };
    if (r.mode === 'payment' && amountCents > sum.availableCents) return { decision: 'declined', reason: 'over_allowance', availableCents: sum.availableCents, shortfallCents: amountCents - sum.availableCents };
    if (amountCents > sum.availableCents) return { decision: 'approved', reason: 'approved_over_budget', availableCents: sum.availableCents, overByCents: amountCents - sum.availableCents };
    return { decision: 'approved', reason: 'within_allowance', availableCents: sum.availableCents };
  }

  function attemptPurchase(state, req) {
    var now = req.now;
    if (!isCents(req.amountCents) || req.amountCents <= 0) fail('Enter an amount above $0.');
    var s = clone(state);
    var card = findCard(s, req.cardId); if (!card) fail('Choose a demo card.');
    if (!findMerchant(s, req.merchantId)) fail('Choose a merchant.');
    var d = decideAuthorization(s, card, req.merchantId, req.amountCents, now);

    // Same card envelope + merchant + amount within 24h of the previous try = same intent.
    var prior = null;
    for (var i = s.attempts.length - 1; i >= 0; i--) {
      var a = s.attempts[i];
      if (a.envelopeId === card.envelopeId && a.merchantId === req.merchantId && a.amountCents === req.amountCents && a.at <= now && now - a.at <= INTENT_WINDOW_MS) { prior = a; break; }
    }
    var attempt = {
      id: nextId(s, 'att'), at: now, cardId: card.id, envelopeId: card.envelopeId, merchantId: req.merchantId,
      amountCents: req.amountCents, decision: d.decision, reason: d.reason,
      intentId: prior ? prior.intentId : null, isRetry: !!prior, note: String(req.note || '').slice(0, 60)
    };
    if (!attempt.intentId) attempt.intentId = nextId(s, 'intent');
    if (d.decision === 'approved') {
      var hold = { id: nextId(s, 'hold'), envelopeId: card.envelopeId, merchantId: req.merchantId, cardId: card.id, amountCents: req.amountCents, createdAt: now, status: 'pending', note: attempt.note };
      s.holds.push(hold);
      attempt.holdId = hold.id;
      if (card.type === 'single_use') card.status = 'used';
    }
    s.attempts.push(attempt);
    var out = clone(d); out.attemptId = attempt.id; out.intentId = attempt.intentId; out.isRetry = attempt.isRetry; out.holdId = attempt.holdId || null;
    return { state: s, result: out };
  }

  // Screen Time shield outcome. No amount is known, so none is recorded.
  function recordShield(state, input, now) {
    var s = clone(state);
    if (!findEnv(s, input.envelopeId)) fail('Envelope not found.');
    if (input.outcome !== 'waited' && input.outcome !== 'unlocked') fail('Unknown shield outcome.');
    s.shieldEvents.push({ id: nextId(s, 'sh'), envelopeId: input.envelopeId, outcome: input.outcome, at: now, unlockMinutes: input.outcome === 'unlocked' ? 10 : 0 });
    return { state: s, result: {} };
  }

  function recordNudge(state, envId, now) {
    var s = clone(state);
    s.nudges.push({ id: nextId(s, 'nd'), envelopeId: envId, at: now });
    return { state: s, result: {} };
  }

  /* ---------------------------------------------------------------- 6 ---- */

  // A purchase the person chose to skip. Linked to an intent when it came from
  // a declined attempt, so the same purchase is never recorded twice.
  function recordForgone(state, input, now) {
    var s = clone(state);
    var label = String(input.label || '').trim().slice(0, 60) || 'Skipped purchase';
    if (input.amountCents !== null && input.amountCents !== undefined && (!isCents(input.amountCents) || input.amountCents < 0)) fail('Enter a valid amount or leave it blank.');
    var existing = null;
    if (input.intentId) s.forgone.forEach(function (f) { if (f.intentId === input.intentId) existing = f; });
    if (existing) { existing.label = label; existing.status = 'forgone'; return { state: s, result: { forgoneId: existing.id, updated: true } }; }
    var f = { id: nextId(s, 'fg'), envelopeId: input.envelopeId || null, merchantId: input.merchantId || null, label: label, amountCents: input.amountCents === undefined ? null : input.amountCents, intentId: input.intentId || null, source: input.source || 'manual', status: 'forgone', at: now };
    s.forgone.push(f);
    return { state: s, result: { forgoneId: f.id } };
  }

  function setForgoneStatus(state, id, status, now) {
    if (status !== 'forgone' && status !== 'bought_later') fail('Unknown status.');
    var s = clone(state);
    var f = null; s.forgone.forEach(function (x) { if (x.id === id) f = x; });
    if (!f) fail('Item not found.');
    f.status = status; f.statusAt = now;
    return { state: s, result: {} };
  }

  function addWish(state, input, now) {
    var s = clone(state);
    var label = String(input.label || '').trim().slice(0, 60);
    if (!label) fail('Name the item you’re thinking about.');
    if (input.amountCents !== null && input.amountCents !== undefined && (!isCents(input.amountCents) || input.amountCents < 0)) fail('Enter a valid price or leave it blank.');
    var existing = null;
    if (input.intentId) s.wishlist.forEach(function (w) { if (w.intentId === input.intentId && w.status === 'waiting') existing = w; });
    if (existing) return { state: state, result: { wishId: existing.id, duplicate: true } };
    var days = input.coolDays || DEFAULT_WISH_COOL_DAYS;
    var w = { id: nextId(s, 'w'), label: label, merchantId: input.merchantId || null, envelopeId: input.envelopeId || null, amountCents: input.amountCents === undefined ? null : input.amountCents, intentId: input.intentId || null, addedAt: now, revisitAt: addDays(now, days), status: 'waiting' };
    s.wishlist.push(w);
    return { state: s, result: { wishId: w.id, revisitAt: w.revisitAt } };
  }

  // status: 'waiting' (wait longer), 'removed' (decided against), 'bought'
  function resolveWish(state, id, status, now, opts) {
    opts = opts || {};
    var s = clone(state);
    var w = null; s.wishlist.forEach(function (x) { if (x.id === id) w = x; });
    if (!w) fail('Item not found.');
    if (status === 'waiting') { w.revisitAt = addDays(Math.max(now, w.revisitAt), DEFAULT_WISH_COOL_DAYS); w.status = 'waiting'; return { state: s, result: {} }; }
    if (status !== 'removed' && status !== 'bought') fail('Unknown status.');
    w.status = status; w.resolvedAt = now; w.afterCoolingOff = now >= w.revisitAt;
    if (status === 'bought' && opts.logSpend && w.envelopeId && isCents(w.amountCents) && w.amountCents > 0) {
      var out = addManualSpend(s, { envelopeId: w.envelopeId, merchantId: w.merchantId, amountCents: w.amountCents, note: w.label }, now);
      return { state: out.state, result: { spendId: out.result.spendId } };
    }
    return { state: s, result: {} };
  }

  function addReflection(state, input, now) {
    var s = clone(state);
    var text = String(input.text || '').trim().slice(0, 400);
    if (!text) fail('Write a few words, or skip this step.');
    s.reflections.push({ id: nextId(s, 'rfl'), text: text, prompt: input.prompt || '', at: now });
    return { state: s, result: {} };
  }

  function setGoal(state, input, now) {
    var s = clone(state);
    var name = String(input.name || '').trim().slice(0, 40);
    if (!name) fail('Name what you’re saving toward.');
    if (!isCents(input.targetCents) || input.targetCents <= 0) fail('Set a target above $0.');
    var prev = s.goal;
    s.goal = { name: name, targetCents: input.targetCents, byDate: input.byDate || null, createdAt: prev ? prev.createdAt : now, reported: prev && input.keepReported ? prev.reported : [] };
    return { state: s, result: {} };
  }

  // Self-reported: the person says they moved money to savings. Not verified.
  function reportSavings(state, amountCents, now) {
    var s = clone(state);
    if (!s.goal) fail('Set a goal first.');
    if (!isCents(amountCents) || amountCents <= 0) fail('Enter an amount above $0.');
    s.goal.reported.push({ id: nextId(s, 'sv'), amountCents: amountCents, at: now });
    return { state: s, result: {} };
  }

  function goalSummary(s, now) {
    if (!s.goal) return null;
    var reported = 0; s.goal.reported.forEach(function (r) { if (r.at <= now) reported += r.amountCents; });
    var pace = null;
    if (s.goal.byDate && s.goal.byDate > s.goal.createdAt) {
      var frac = Math.min(1, Math.max(0, (now - s.goal.createdAt) / (s.goal.byDate - s.goal.createdAt)));
      var expected = Math.round(s.goal.targetCents * frac);
      pace = { expectedCents: expected, onTrack: reported >= expected };
    }
    return { name: s.goal.name, targetCents: s.goal.targetCents, byDate: s.goal.byDate, reportedCents: reported, verifiedCents: null, pace: pace };
  }

  /* ---------------------------------------------------------------- 7 ---- */

  function daysWithinBudget(s, now) {
    var day = startOfDay(s.startedAt), last = startOfDay(now);
    var within = 0, total = 0, streak = 0, best = 0;
    while (day <= last) {
      var next = new Date(new Date(day).getFullYear(), new Date(day).getMonth(), new Date(day).getDate() + 1).getTime();
      var asOf = Math.min(next - 1, now);
      var ok = true, any = false;
      s.envelopes.forEach(function (env) {
        if (env.createdAt > asOf || !rulesAt(env, asOf).active) return;
        any = true;
        var from = periodStart(env.cadence, asOf), to = periodEnd(env.cadence, asOf);
        if (completedInWindow(s, env.id, from, to, asOf) > rulesAt(env, asOf).budgetCents) ok = false;
      });
      if (any) {
        total++;
        if (ok) { within++; streak++; best = Math.max(best, streak); } else streak = 0;
      }
      day = next;
    }
    return { within: within, total: total, streak: streak, best: best };
  }

  function intents(s, now) {
    var map = {}, order = [];
    s.attempts.forEach(function (a) {
      if (a.at > now) return;
      var g = map[a.intentId];
      if (!g) { g = map[a.intentId] = { intentId: a.intentId, envelopeId: a.envelopeId, merchantId: a.merchantId, amountCents: a.amountCents, firstAt: a.at, lastAt: a.at, attempts: 0, declines: 0, approved: false, reasons: [] }; order.push(g); }
      g.attempts++; g.lastAt = a.at;
      if (a.decision === 'declined') { g.declines++; if (g.reasons.indexOf(a.reason) < 0) g.reasons.push(a.reason); }
      else g.approved = true;
    });
    return order;
  }

  function progress(s, now) {
    var ints = intents(s, now);
    var declinedIntents = ints.filter(function (g) { return g.declines > 0 && !g.approved; });
    var declineAttempts = 0; ints.forEach(function (g) { declineAttempts += g.declines; });
    var declinedValue = 0; declinedIntents.forEach(function (g) { declinedValue += g.amountCents; });

    var shields = s.shieldEvents.filter(function (e) { return e.at <= now; });
    var waited = shields.filter(function (e) { return e.outcome === 'waited'; }).length;
    var nudges = s.nudges.filter(function (e) { return e.at <= now; }).length;

    var forgone = s.forgone.filter(function (f) { return f.at <= now && f.status === 'forgone'; });
    var forgoneValue = 0, forgoneUnknown = 0;
    forgone.forEach(function (f) { if (isCents(f.amountCents)) forgoneValue += f.amountCents; else forgoneUnknown++; });
    var boughtLater = s.forgone.filter(function (f) { return f.status === 'bought_later'; });

    var periodCompleted = 0, periodPending = 0;
    activeEnvelopes(s, now).forEach(function (e) { var x = envelopeSummary(s, e.id, now); periodCompleted += x.completedCents; periodPending += x.pendingCents; });
    var allTime = 0; s.spend.forEach(function (x) { if (x.postedAt <= now) allTime += x.amountCents - refundedCents(s, x.id, now); });

    return {
      interventions: { total: shields.length + declinedIntents.length + nudges, shields: shields.length, shieldsWaited: waited, declines: declinedIntents.length, nudges: nudges },
      declined: { valueCents: declinedValue, uniqueCount: declinedIntents.length, attemptCount: declineAttempts, intents: declinedIntents },
      forgone: { valueCents: forgoneValue, count: forgone.length, unknownAmountCount: forgoneUnknown, boughtLaterCount: boughtLater.length },
      completed: { periodCents: periodCompleted, pendingCents: periodPending, allTimeCents: allTime },
      days: daysWithinBudget(s, now),
      verifiedSavings: null,
      goal: goalSummary(s, now)
    };
  }

  function milestones(s, now) {
    var p = progress(s, now);
    var wishAfterCool = s.wishlist.some(function (w) { return w.status !== 'waiting' && w.afterCoolingOff; });
    var fullPeriod = s.envelopes.some(function (env) {
      var cur = periodStart(env.cadence, now);
      var prevStart = periodStart(env.cadence, cur - 1);
      if (env.createdAt > prevStart) return false;
      return completedInWindow(s, env.id, prevStart, cur, now) <= rulesAt(env, cur - 1).budgetCents;
    });
    var firstPause = p.interventions.shieldsWaited > 0 || p.forgone.count > 0 || s.wishlist.length > 0;
    return [
      { id: 'first_pause', title: 'First deliberate pause', detail: 'You stopped before a purchase and chose what happened next.', done: firstPause },
      { id: 'reflection', title: 'Named what you felt', detail: 'You wrote a reflection about a moment you wanted to buy.', done: s.reflections.length > 0 },
      { id: 'streak7', title: 'Seven days within budget', detail: 'Every envelope stayed within its budget for a week in a row.', done: p.days.best >= 7, progress: Math.min(7, p.days.best) + ' of 7 days' },
      { id: 'wish', title: 'Waited out a want', detail: 'You revisited a wishlist item after its cooling-off ended.', done: wishAfterCool },
      { id: 'period', title: 'A full period kept', detail: 'An envelope finished a whole week or month within its budget.', done: fullPeriod }
    ];
  }

  /* ---------------------------------------------------------------- seed -- */

  // Fictional demo history relative to `now`, built through the engine itself
  // so the ledger is internally consistent.
  function seedDemoState(now) {
    var start = startOfDay(addDays(now, -24));
    var s = emptyState(start);
    function run(out) { s = out.state; return out.result; }
    s.profile.name = 'Sam';
    s.focus = ['Online shopping', 'Food delivery', 'Home decor'];
    var amazon = run(createEnvelope(s, { merchantId: 'amazon', cadence: 'monthly', budgetCents: 15000, mode: 'payment', commitment: true, coolingHours: 48 }, start));
    var target = run(createEnvelope(s, { merchantId: 'target', cadence: 'monthly', budgetCents: 10000, mode: 'access', commitment: false, coolingHours: 24 }, start));
    var dash = run(createEnvelope(s, { merchantId: 'doordash', cadence: 'weekly', budgetCents: 4500, mode: 'reminder', commitment: false, coolingHours: 24 }, start));
    var hearth = run(createEnvelope(s, { merchantId: 'hearth', cadence: 'monthly', budgetCents: 6000, mode: 'payment', commitment: true, coolingHours: 72 }, start));
    var t = function (days, hours) { return now - days * DAY - (hours || 0) * HOUR; };

    run(setGoal(s, { name: 'Lisbon in spring', targetCents: 180000, byDate: new Date(new Date(now).getFullYear() + 1, 3, 1).getTime() }, start));
    s.goal.createdAt = start;
    run(reportSavings(s, 25000, t(14)));
    run(reportSavings(s, 17000, t(2)));

    // Amazon: card purchases, a refund, a reversal, a declined retry, a pending hold.
    var a1 = run(attemptPurchase(s, { cardId: amazon.cardId, merchantId: 'amazon', amountCents: 3499, now: t(9, 3), note: 'Phone case' }));
    run(captureHold(s, a1.holdId, 3499, t(8)));
    var a2 = run(attemptPurchase(s, { cardId: amazon.cardId, merchantId: 'amazon', amountCents: 2200, now: t(6, 5), note: 'Desk lamp' }));
    var c2 = run(captureHold(s, a2.holdId, 2200, t(5)));
    run(refundSpend(s, c2.spendId, 2200, t(4)));
    // Above the whole monthly budget, so it is declined whatever day the demo starts.
    var a3 = run(attemptPurchase(s, { cardId: amazon.cardId, merchantId: 'amazon', amountCents: 16900, now: t(5, 2), note: 'Headphones' }));
    run(attemptPurchase(s, { cardId: amazon.cardId, merchantId: 'amazon', amountCents: 16900, now: t(5, 1), note: 'Headphones' }));
    run(addWish(s, { label: 'Noise-cancelling headphones', merchantId: 'amazon', envelopeId: amazon.envelopeId, amountCents: 16900, intentId: a3.intentId, coolDays: 4 }, t(5, 1)));
    var a4 = run(attemptPurchase(s, { cardId: amazon.cardId, merchantId: 'amazon', amountCents: 1847, now: t(3, 4), note: 'Notebooks' }));
    run(captureHold(s, a4.holdId, 1847, t(2)));
    var a5 = run(attemptPurchase(s, { cardId: amazon.cardId, merchantId: 'amazon', amountCents: 999, now: t(1, 6), note: 'Phone charger' }));
    run(releaseHold(s, a5.holdId, t(0, 20)));
    run(attemptPurchase(s, { cardId: amazon.cardId, merchantId: 'amazon', amountCents: 1289, now: t(0, 2), note: 'Coffee filters' }));

    // Target: shopping access restriction (shield) plus manual entries.
    run(addManualSpend(s, { envelopeId: target.envelopeId, amountCents: 4120, occurredAt: t(8), note: 'Household basics' }, t(8)));
    run(addManualSpend(s, { envelopeId: target.envelopeId, amountCents: 1675, occurredAt: t(1), note: 'Birthday card and wrap' }, t(1)));
    run(recordShield(s, { envelopeId: target.envelopeId, outcome: 'waited' }, t(7, 2)));
    run(recordForgone(s, { envelopeId: target.envelopeId, merchantId: 'target', label: 'Air fryer', amountCents: 8999, source: 'shield' }, t(7, 2)));
    run(recordShield(s, { envelopeId: target.envelopeId, outcome: 'unlocked' }, t(4, 6)));
    run(recordShield(s, { envelopeId: target.envelopeId, outcome: 'waited' }, t(0, 5)));

    // DoorDash: reminders only.
    run(addManualSpend(s, { envelopeId: dash.envelopeId, amountCents: 1800, occurredAt: t(12), note: 'Thai takeout' }, t(12)));
    run(addManualSpend(s, { envelopeId: dash.envelopeId, amountCents: 3150, occurredAt: t(10), note: 'Pizza night' }, t(10)));
    run(addManualSpend(s, { envelopeId: dash.envelopeId, amountCents: 2350, occurredAt: t(1, 4), note: 'Ramen' }, t(1, 4)));
    run(recordNudge(s, dash.envelopeId, t(1, 4)));

    // Hearth & Loom: custom merchant.
    var h1 = run(attemptPurchase(s, { cardId: hearth.cardId, merchantId: 'hearth', amountCents: 4800, now: t(15), note: 'Ceramic planter' }));
    run(captureHold(s, h1.holdId, 4800, t(14)));
    run(addWish(s, { label: 'Linen throw blanket', merchantId: 'hearth', envelopeId: hearth.envelopeId, amountCents: 6400, coolDays: 7 }, t(4)));

    run(addReflection(s, { text: 'Work was stressful and buying felt like a reward. Sleeping on it helped, and I didn’t miss it the next day.', prompt: 'What was going on when you wanted it?' }, t(5)));
    s.onboarded = false;
    return s;
  }

  // Apply onboarding answers on top of whatever state exists.
  function completeOnboarding(state, a, now) {
    var s = clone(state);
    function run(out) { s = out.state; return out.result; }
    s.profile.name = String(a.name || '').trim().slice(0, 30);
    s.focus = (a.focus || []).slice(0, 8);
    if (a.goal) {
      var sameGoal = s.goal && s.goal.name === a.goal.name;
      run(setGoal(s, { name: a.goal.name, targetCents: a.goal.targetCents, byDate: a.goal.byDate, keepReported: sameGoal }, now));
    }
    var merchantId = a.envelope.merchantId;
    if (a.envelope.customName) merchantId = run(addMerchant(s, { name: a.envelope.customName, domain: a.envelope.customDomain })).merchantId;
    var existing = activeEnvelopes(s, now).filter(function (e) { return e.merchantId === merchantId; })[0];
    var envId;
    if (existing) {
      envId = existing.id;
      run(configureEnvelope(s, envId, { budgetCents: a.envelope.budgetCents, mode: a.envelope.mode, commitment: a.envelope.commitment, coolingHours: a.envelope.coolingHours, cadence: a.envelope.cadence }, now));
    } else {
      envId = run(createEnvelope(s, { merchantId: merchantId, cadence: a.envelope.cadence, budgetCents: a.envelope.budgetCents, mode: a.envelope.mode, commitment: a.envelope.commitment, coolingHours: a.envelope.coolingHours }, now)).envelopeId;
    }
    s.onboarded = true;
    s.firstEnvelopeId = envId;
    return { state: s, result: { envelopeId: envId } };
  }

  /* ---------------------------------------------------------------- 8 ---- */

  function runSelfTests() {
    var T0 = new Date(2026, 9, 14, 12, 0, 0).getTime(); // Wed Oct 14 2026, noon local
    var results = [];
    function test(name, fn) {
      try { fn(); results.push({ name: name, pass: true }); }
      catch (e) { results.push({ name: name, pass: false, error: e.message }); }
    }
    function eq(a, b, label) { if (a !== b) throw new Error((label || 'value') + ': expected ' + b + ', got ' + a); }
    function throws(fn, label) { var ok = false; try { fn(); } catch (e) { ok = true; } if (!ok) throw new Error(label + ' should have been rejected'); }
    function fixture(opts) {
      opts = opts || {};
      var s = emptyState(T0 - 3 * DAY);
      var r = createEnvelope(s, { merchantId: 'amazon', cadence: opts.cadence || 'monthly', budgetCents: 10000, mode: 'payment', commitment: opts.commitment !== false, coolingHours: 48 }, T0 - 3 * DAY);
      return { s: r.state, env: r.result.envelopeId, card: r.result.cardId };
    }
    function avail(s, env, t) { return envelopeSummary(s, env, t === undefined ? T0 : t).availableCents; }

    test('Exact remaining allowance is approved', function () {
      var f = fixture();
      var s = addManualSpend(f.s, { envelopeId: f.env, amountCents: 2501 }, T0).state;
      eq(avail(s, f.env), 7499, 'available before');
      var r = attemptPurchase(s, { cardId: f.card, merchantId: 'amazon', amountCents: 7499, now: T0 });
      eq(r.result.decision, 'approved', 'decision');
      eq(avail(r.state, f.env), 0, 'available after');
    });
    test('One cent above the remaining allowance is declined', function () {
      var f = fixture();
      var s = addManualSpend(f.s, { envelopeId: f.env, amountCents: 2501 }, T0).state;
      var r = attemptPurchase(s, { cardId: f.card, merchantId: 'amazon', amountCents: 7500, now: T0 });
      eq(r.result.decision, 'declined', 'decision'); eq(r.result.reason, 'over_allowance', 'reason'); eq(r.result.shortfallCents, 1, 'shortfall');
    });
    test('Wrong-merchant attempt is declined even within budget', function () {
      var f = fixture();
      var r = attemptPurchase(f.s, { cardId: f.card, merchantId: 'target', amountCents: 100, now: T0 });
      eq(r.result.reason, 'wrong_merchant', 'reason');
    });
    test('Declined attempts add no spending and no holds', function () {
      var f = fixture();
      var s = attemptPurchase(f.s, { cardId: f.card, merchantId: 'amazon', amountCents: 50000, now: T0 }).state;
      s = attemptPurchase(s, { cardId: f.card, merchantId: 'target', amountCents: 500, now: T0 }).state;
      var x = envelopeSummary(s, f.env, T0);
      eq(x.completedCents, 0, 'completed'); eq(x.pendingCents, 0, 'pending'); eq(s.holds.length, 0, 'holds');
    });
    test('Retries of the same purchase count once', function () {
      var f = fixture();
      var s = f.s;
      for (var i = 0; i < 3; i++) s = attemptPurchase(s, { cardId: f.card, merchantId: 'amazon', amountCents: 20000, now: T0 + i * 60000 }).state;
      s = attemptPurchase(s, { cardId: f.card, merchantId: 'amazon', amountCents: 30000, now: T0 + 5 * 60000 }).state;
      var p = progress(s, T0 + DAY / 2);
      eq(p.declined.attemptCount, 4, 'attempts'); eq(p.declined.uniqueCount, 2, 'unique'); eq(p.declined.valueCents, 50000, 'value');
      eq(p.interventions.declines, 2, 'interventions');
    });
    test('A retry more than 24 hours later is a new intent', function () {
      var f = fixture();
      var s = attemptPurchase(f.s, { cardId: f.card, merchantId: 'amazon', amountCents: 20000, now: T0 }).state;
      s = attemptPurchase(s, { cardId: f.card, merchantId: 'amazon', amountCents: 20000, now: T0 + DAY + 1 }).state;
      eq(progress(s, T0 + 2 * DAY).declined.uniqueCount, 2, 'unique');
    });
    test('A declined purchase approved later leaves declined value', function () {
      var f = fixture({ commitment: false });
      var s = attemptPurchase(f.s, { cardId: f.card, merchantId: 'amazon', amountCents: 12000, now: T0 }).state;
      s = requestChange(s, f.env, 'budget', 15000, T0 + 1000).state;
      var r = attemptPurchase(s, { cardId: f.card, merchantId: 'amazon', amountCents: 12000, now: T0 + 2000 });
      eq(r.result.decision, 'approved', 'retry decision'); eq(r.result.isRetry, true, 'retry flag');
      eq(progress(r.state, T0 + 3000).declined.valueCents, 0, 'declined value');
    });
    test('Pending holds reserve allowance until captured', function () {
      var f = fixture();
      var r = attemptPurchase(f.s, { cardId: f.card, merchantId: 'amazon', amountCents: 4000, now: T0 });
      var x = envelopeSummary(r.state, f.env, T0);
      eq(x.pendingCents, 4000, 'pending'); eq(x.completedCents, 0, 'completed'); eq(x.availableCents, 6000, 'available');
      var c = captureHold(r.state, r.result.holdId, undefined, T0 + HOUR);
      x = envelopeSummary(c.state, f.env, T0 + HOUR);
      eq(x.pendingCents, 0, 'pending after'); eq(x.completedCents, 4000, 'completed after'); eq(x.availableCents, 6000, 'available after');
      throws(function () { captureHold(c.state, r.result.holdId, undefined, T0 + 2 * HOUR); }, 'Second capture');
    });
    test('Released hold restores the allowance', function () {
      var f = fixture();
      var r = attemptPurchase(f.s, { cardId: f.card, merchantId: 'amazon', amountCents: 4000, now: T0 });
      var s = releaseHold(r.state, r.result.holdId, T0 + HOUR).state;
      eq(avail(s, f.env, T0 + HOUR), 10000, 'available');
      throws(function () { releaseHold(s, r.result.holdId, T0 + 2 * HOUR); }, 'Second release');
    });
    test('Partial capture releases the remainder', function () {
      var f = fixture();
      var r = attemptPurchase(f.s, { cardId: f.card, merchantId: 'amazon', amountCents: 4000, now: T0 });
      var c = captureHold(r.state, r.result.holdId, 3000, T0 + HOUR);
      eq(c.result.releasedCents, 1000, 'released'); eq(avail(c.state, f.env, T0 + HOUR), 7000, 'available');
    });
    test('Refunds restore allowance once and cannot exceed the purchase', function () {
      var f = fixture();
      var s = addManualSpend(f.s, { envelopeId: f.env, amountCents: 6000 }, T0).state;
      var sp = s.spend[0].id;
      s = refundSpend(s, sp, 2500, T0 + HOUR).state;
      eq(avail(s, f.env, T0 + HOUR), 6500, 'after partial refund');
      throws(function () { refundSpend(s, sp, 3501, T0 + 2 * HOUR); }, 'Over-refund');
      s = refundSpend(s, sp, 3500, T0 + 2 * HOUR).state;
      eq(avail(s, f.env, T0 + 2 * HOUR), 10000, 'after full refund');
      throws(function () { refundSpend(s, sp, 1, T0 + 3 * HOUR); }, 'Refund beyond full');
    });
    test('A refund of last period’s purchase does not inflate this period', function () {
      var f = fixture({ cadence: 'weekly' });
      var s = addManualSpend(f.s, { envelopeId: f.env, amountCents: 5000, occurredAt: T0 }, T0).state;
      var nextWeek = T0 + 7 * DAY;
      s = refundSpend(s, s.spend[0].id, 5000, nextWeek).state;
      eq(avail(s, f.env, nextWeek), 10000, 'next period available');
      eq(envelopeSummary(s, f.env, nextWeek).completedCents, 0, 'next period completed');
    });
    test('Budget reset starts a fresh allowance', function () {
      var f = fixture({ cadence: 'weekly' });
      var s = addManualSpend(f.s, { envelopeId: f.env, amountCents: 9000 }, T0).state;
      var r = attemptPurchase(s, { cardId: f.card, merchantId: 'amazon', amountCents: 1000, now: T0 }).state;
      eq(avail(r, f.env, T0), 0, 'this week');
      var monday = periodEnd('weekly', T0);
      eq(avail(r, f.env, monday), 10000, 'next week');
      eq(avail(r, f.env, monday - 1), 0, 'last millisecond of this week');
    });
    test('Budget increase waits for the cooling-off period', function () {
      var f = fixture();
      var r = requestChange(f.s, f.env, 'budget', 20000, T0);
      eq(r.result.delayed, true, 'delayed');
      eq(r.result.effectiveAt, T0 + 48 * HOUR, 'effective time');
      eq(envelopeSummary(r.state, f.env, T0 + 48 * HOUR - 1).budgetCents, 10000, 'before');
      eq(envelopeSummary(r.state, f.env, T0 + 48 * HOUR).budgetCents, 20000, 'after');
    });
    test('Budget reduction is immediate and replaces a pending increase', function () {
      var f = fixture();
      var s = requestChange(f.s, f.env, 'budget', 20000, T0).state;
      var r = requestChange(s, f.env, 'budget', 8000, T0 + HOUR);
      eq(r.result.delayed, false, 'delayed');
      eq(envelopeSummary(r.state, f.env, T0 + HOUR).budgetCents, 8000, 'now');
      eq(envelopeSummary(r.state, f.env, T0 + 72 * HOUR).budgetCents, 8000, 'after old timer');
    });
    test('Cancelled increase never takes effect', function () {
      var f = fixture();
      var r = requestChange(f.s, f.env, 'budget', 20000, T0);
      var s = cancelPending(r.state, f.env, 'budget', r.result.effectiveAt, T0 + HOUR).state;
      eq(envelopeSummary(s, f.env, T0 + 100 * HOUR).budgetCents, 10000, 'budget');
    });
    test('Re-requesting a pending increase keeps the original timer', function () {
      var f = fixture();
      var s = requestChange(f.s, f.env, 'budget', 20000, T0).state;
      var r = requestChange(s, f.env, 'budget', 20000, T0 + 10 * HOUR);
      eq(r.result.effectiveAt, T0 + 48 * HOUR, 'effective time');
    });
    test('Without commitment mode, increases apply immediately', function () {
      var f = fixture({ commitment: false });
      var r = requestChange(f.s, f.env, 'budget', 20000, T0);
      eq(r.result.delayed, false, 'delayed'); eq(envelopeSummary(r.state, f.env, T0).budgetCents, 20000, 'budget');
    });
    test('Weakening restrictions or leaving commitment mode is delayed', function () {
      var f = fixture();
      var m = requestChange(f.s, f.env, 'mode', 'reminder', T0);
      eq(m.result.delayed, true, 'mode delayed');
      eq(attemptPurchase(m.state, { cardId: f.card, merchantId: 'amazon', amountCents: 50000, now: T0 + HOUR }).result.decision, 'declined', 'still enforced');
      var c = requestChange(f.s, f.env, 'commitment', false, T0);
      eq(c.result.delayed, true, 'commitment delayed');
      var d = requestChange(f.s, f.env, 'active', false, T0);
      eq(d.result.delayed, true, 'delete delayed');
      eq(activeEnvelopes(d.state, T0 + 47 * HOUR).length, 1, 'still active');
      eq(activeEnvelopes(d.state, T0 + 48 * HOUR).length, 0, 'closed after');
    });
    test('Single-use card declines after its first approval', function () {
      var f = fixture();
      var c = createCard(f.s, f.env, 'single_use', T0);
      var r1 = attemptPurchase(c.state, { cardId: c.result.cardId, merchantId: 'amazon', amountCents: 1000, now: T0 });
      eq(r1.result.decision, 'approved', 'first');
      var r2 = attemptPurchase(r1.state, { cardId: c.result.cardId, merchantId: 'amazon', amountCents: 1000, now: T0 + 1000 });
      eq(r2.result.reason, 'card_used', 'second');
    });
    test('Days within budget ignore declined attempts', function () {
      var f = fixture();
      var s = attemptPurchase(f.s, { cardId: f.card, merchantId: 'amazon', amountCents: 90000, now: T0 }).state;
      var d = daysWithinBudget(s, T0);
      eq(d.within, d.total, 'all days within');
    });
    test('Amounts parse to whole cents', function () {
      eq(toCents('10.1'), 1010, '10.1'); eq(toCents('$1,204.99'), 120499, 'formatted'); eq(toCents('.5'), 50, '.5');
      eq(toCents('0.005'), null, 'three decimals'); eq(toCents('abc'), null, 'text'); eq(toCents('-4'), null, 'negative');
      eq(formatCents(120499), '$1,204.99', 'format');
    });
    return results;
  }

  var api = {
    STATE_VERSION: STATE_VERSION, HOUR: HOUR, DAY: DAY, MODE_RANK: MODE_RANK,
    toCents: toCents, formatCents: formatCents, startOfDay: startOfDay, addDays: addDays, periodStart: periodStart, periodEnd: periodEnd,
    emptyState: emptyState, seedDemoState: seedDemoState, completeOnboarding: completeOnboarding,
    rulesAt: rulesAt, pendingChanges: pendingChanges, activeEnvelopes: activeEnvelopes, envelopeSummary: envelopeSummary,
    findEnv: findEnv, findMerchant: findMerchant, findCard: findCard, cardsFor: cardsFor, refundedCents: refundedCents,
    addMerchant: addMerchant, createEnvelope: createEnvelope, requestChange: requestChange, cancelPending: cancelPending, configureEnvelope: configureEnvelope,
    addManualSpend: addManualSpend, captureHold: captureHold, releaseHold: releaseHold, refundSpend: refundSpend,
    createCard: createCard, attemptPurchase: attemptPurchase, recordShield: recordShield, recordNudge: recordNudge,
    recordForgone: recordForgone, setForgoneStatus: setForgoneStatus, addWish: addWish, resolveWish: resolveWish,
    addReflection: addReflection, setGoal: setGoal, reportSavings: reportSavings, goalSummary: goalSummary,
    progress: progress, intents: intents, milestones: milestones, daysWithinBudget: daysWithinBudget,
    runSelfTests: runSelfTests
  };
  root.ArcaEngine = api;
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
})(typeof window !== 'undefined' ? window : this);
