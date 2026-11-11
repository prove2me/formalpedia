-- Prove2me | Theorems.Thm_FiniteGroupTesting_LinearQuery_lemma_3_9
-- name    : FiniteGroupTesting.LinearQuery.lemma_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:09:33.338697+00:00
-- url     : https://prove2.me/theorems/b4ca92f4-6b8f-4e04-b919-6e14c0b5dddd
-- title:
--   Lemma 3.9 — perfect completeness
-- statement:
--   For $n\ge4$ and $0<\epsilon<1/2$, the specified Section 3 tester, on every genuine group operation, satisfies
--
--   $$\Pr[\mathrm{accept}]=1.$$
--
--   This holds for every fixed positive pair of preprocessing integers $A,B$, including the sufficiently large ones used in soundness. Three failed preprocessing attempts explicitly accept; on a success, the evaluator is the true multiplication. No success-of-preprocessing hypothesis is imposed on the input or randomness.
--
--   Differences from the source:
--   - encoding: [n] = {1,...,n} and its subsets → Fin n with i relabelled i+1, and indexed stored subsets; reason: bijections preserve every table entry, group, and probability; unused ambient labels are fixed by stored permutations
--   - reading: explicit-permutation constant-time lookup and real accuracy parameters → charged unit-cost randomized RAM semantics with exact uniform-interval sampling and one charged table-independent integer accuracy conversion; reason: the paper specifies no bit-machine or real-input representation; subsequent operations are finite-word array access, arithmetic, comparisons and loops
--   - encoding: O(log n) sampled labels and O(log n) word depth → fixed positive integers A,B give A ceil(log_2 n) samples and B ceil(log_2 n) depth; reason: A,B are chosen once to dominate Corollary 2.4 constants, before every input; extra generators and depth preserve success
--   - generalization: the sufficiently large fixed preprocessing constants used by the source tester → every pair of positive fixed integers A,B; reason: perfect completeness also holds when preprocessing often fails, because all three failures accept; the source choices are included
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 24, Lemma 3.9

import Definitions.Def_FiniteGroupTesting_LinearQuery_Tester

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery
open OracleRun

/-- Lemma 3.9, p. 24. All preprocessing failures accept, for any fixed positive A,B. -/
theorem lemma_3_9 (A B n : ℕ) (hA : 0 < A) (hB : 0 < B) (hn : 4 ≤ n)
    (ε : ℝ) (he : 0 < ε) (he2 : ε < 1/2) (op : Table n) (hgroup : IsGroupLaw op) :
    probability op (· = true) (sectionTester A B n ε) = 1 := by sorry

end FiniteGroupTesting.LinearQuery
