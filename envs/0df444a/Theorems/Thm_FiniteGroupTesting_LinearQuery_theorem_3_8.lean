-- Prove2me | Theorems.Thm_FiniteGroupTesting_LinearQuery_theorem_3_8
-- name    : FiniteGroupTesting.LinearQuery.theorem_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:11:22.975617+00:00
-- url     : https://prove2.me/theorems/32cdaedf-68f5-4f2d-92f7-303eab6883b4
-- title:
--   Theorem 3.8 — randomized regularity test
-- statement:
--   Let $X$ have size $k\ge1$, let $e\in X$, and let $m$ explicitly stored permutations generate $P\le\operatorname{Sym}(X)$. For every $0<\delta<1$, the specified orbit-tree test accepts regular actions with probability one, rejects nonregular actions with probability at least $1-\delta$, and rejects nontransitive actions on every execution. It makes no original-table queries. A universal $C>0$ bounds every run by
--
--   $$Ck(m+1)\bigl(1+\lceil\log_2\lceil1/\delta\rceil\rceil\bigr).$$
--
--   This includes setup, integer round computation and $m=0$, and gives the printed $O(km\log(1/\delta))$ when $m\ge1$ and $\delta$ is bounded away from one. For no generators the test accepts exactly on a singleton. The constant precedes every set, generator family and failure parameter.
--
--   Differences from the source:
--   - encoding: [n] = {1,...,n} and its subsets → Fin n with i relabelled i+1, and indexed stored subsets; reason: bijections preserve every table entry, group, and probability; unused ambient labels are fixed by stored permutations
--   - reading: explicit-permutation constant-time lookup and real accuracy parameters → charged unit-cost randomized RAM semantics with exact uniform-interval sampling and one charged table-independent integer accuracy conversion; reason: the paper specifies no bit-machine or real-input representation; subsequent operations are finite-word array access, arithmetic, comparisons and loops
--   - reading: O(km log(1/delta)) and an unspecified logarithm base → C k (m+1)(1+ceil(log_2 ceil(1/delta))) for all delta in (0,1), with an empty-generator branch; reason: the operational bound retains setup near delta=1 and handles m=0; base 2 gives 2^(-r)≤delta, and the printed asymptotic follows on its usual positive-m small-delta regime
--   - reading: there is a randomized algorithm running in the stated time → the specified program regularityTest (the orbit-tree test of the proof) satisfies the guarantees; reason: in the run semantics, transitions between charged nodes are arbitrary Lean functions, so an existential over programs would leave computation uncharged; fixing the paper's own algorithm gives the time bound content and implies the existential claim
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 20–22, Theorem 3.8

import Definitions.Def_FiniteGroupTesting_LinearQuery_ActionAssertions

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery
open OracleRun

/-- Theorem 3.8, pp. 20--22. Padded cost includes setup and the empty-generator case. -/
theorem theorem_3_8 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (a : StoredAction n) (e : Fin n)
      (δ : ℝ), a.Valid → e ∈ a.domain.carrier → 0 < δ → δ < 1 →
      (∀ op : Table n, RegularOn a.group a.domain.carrier →
        probability op (· = true) (regularityTest a e δ) = 1) ∧
      (∀ op : Table n, ¬ RegularOn a.group a.domain.carrier →
        1 - δ ≤ probability op (· = false) (regularityTest a e δ)) ∧
      (∀ (op : Table n) (r : Outcome n Bool), Executes op (regularityTest a e δ) r →
        (¬ TransitiveOn a.group a.domain.carrier → r.value = false)) ∧
      ResourceBound (regularityTest a e δ) 0
        (C * a.domain.count * (a.degree + 1) * (1 + (Nat.clog 2 ⌈1 / δ⌉₊ : ℝ))) := by sorry

end FiniteGroupTesting.LinearQuery
