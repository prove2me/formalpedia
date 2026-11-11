-- Prove2me | Theorems.Thm_FiniteGroupTesting_LinearQuery_lemma_3_10
-- name    : FiniteGroupTesting.LinearQuery.lemma_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:09:25.021826+00:00
-- url     : https://prove2.me/theorems/13728d2e-d575-4d03-9e35-06530ce392dc
-- title:
--   Lemma 3.10 — soundness strictly above two thirds
-- statement:
--   There are fixed positive implementation integers $A,B$, chosen before $n,\epsilon$, the input and all randomness, such that for every $n\ge4$, $0<\epsilon<1/2$ and operation that is $\epsilon$-far from every group law on the same carrier,
--
--   $$\Pr[\mathrm{reject}]>\frac23.$$
--
--   The tested program uses $\bar\epsilon=\max\{\epsilon,n^{-2}\}$, $q=\lceil5/\bar\epsilon\rceil$, at most three fresh preprocessing attempts and regularity error $1/(100\lceil\log_2n\rceil)$. The source's false-acceptance accounting is $1/100+1/27+1/100<1/3$, with comparison miss probability at most $e^{-5}<1/100$. These are unconditional guarantees for arbitrary tables; accepted nonregular intermediate actions remain possible executions.
--
--   Differences from the source:
--   - encoding: [n] = {1,...,n} and its subsets → Fin n with i relabelled i+1, and indexed stored subsets; reason: bijections preserve every table entry, group, and probability; unused ambient labels are fixed by stored permutations
--   - reading: explicit-permutation constant-time lookup and real accuracy parameters → charged unit-cost randomized RAM semantics with exact uniform-interval sampling and one charged table-independent integer accuracy conversion; reason: the paper specifies no bit-machine or real-input representation; subsequent operations are finite-word array access, arithmetic, comparisons and loops
--   - encoding: O(log n) sampled labels and O(log n) word depth → fixed positive integers A,B give A ceil(log_2 n) samples and B ceil(log_2 n) depth; reason: A,B are chosen once to dominate Corollary 2.4 constants, before every input; extra generators and depth preserve success
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 24, Lemma 3.10

import Definitions.Def_FiniteGroupTesting_LinearQuery_Tester

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery
open OracleRun

/-- Lemma 3.10, p. 24: strict >2/3, with universal preprocessing constants. -/
theorem lemma_3_10 :
    ∃ A B : ℕ, 0 < A ∧ 0 < B ∧ ∀ (n : ℕ), 4 ≤ n →
      ∀ ε : ℝ, 0 < ε → ε < 1/2 → ∀ op : Table n, Far ε op →
        (2/3 : ℝ) < probability op (· = false) (sectionTester A B n ε) := by sorry

end FiniteGroupTesting.LinearQuery
