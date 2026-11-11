-- Prove2me | Theorems.Thm_FiniteGroupTesting_LinearQuery_lemma_3_5
-- name    : FiniteGroupTesting.LinearQuery.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:12:04.426735+00:00
-- url     : https://prove2.me/theorems/45d2264b-636a-407a-88bb-3f0dc785a752
-- title:
--   Lemma 3.5 — successful and rejecting query costs
-- statement:
--   For any completed Algorithm 1 execution with old size $h=|H|$ and ambient size $n$, let $Q$ be the number of actual original-table queries. Then
--
--   $$\text{success on }K:\ Q\le2|K|-h,\qquad\text{rejection}:\ Q\le3n.$$
--
--   The rejecting-run bound instantiates the printed $O(n)$ using the proof's counts $n+n+h\le3n$. Copying stored generators makes no multiplication-table queries. Integer subtraction expresses $2|K|-h$ without truncation. Both bounds include all executed failure checks.
--
--   Differences from the source:
--   - encoding: [n] = {1,...,n} and its subsets → Fin n with i relabelled i+1, and indexed stored subsets; reason: bijections preserve every table entry, group, and probability; unused ambient labels are fixed by stored permutations
--   - encoding: the queue loop stops upon rejection or an empty queue → at most n queue iterations, with charged inert iterations after stopping; reason: disjoint discovery permits at most n pops; the same queries and output result, and the padding costs only O(n) time
--   - encoding: rejecting executions use O(n) queries → rejecting executions use at most 3n queries; reason: the source proof counts at most n row queries, n successful-block queries and h final-block queries, with h≤n
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 18, Lemma 3.5

import Definitions.Def_FiniteGroupTesting_LinearQuery_ActionAssertions

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery
open OracleRun

/-- Lemma 3.5, p. 18. The failed-run constant 3 follows from the proof's n+n+h count. -/
theorem lemma_3_5 {n : ℕ} (op : Table n) (a : StoredAction n) (e b : Fin n)
    (hinput : ExtensionInput a e b) (r : Outcome n (Option (ExtensionOutput n)))
    (hr : Executes op (exploreExtension a e b) r) :
    (∀ out : ExtensionOutput n, r.value = some out →
      (r.transcript.length : ℤ) ≤ 2 * (out.action.domain.count : ℤ) - a.domain.count) ∧
    (r.value = none → r.transcript.length ≤ 3 * n) := by sorry

end FiniteGroupTesting.LinearQuery
