-- Prove2me | Theorems.Thm_FiniteGroupTesting_LinearQuery_theorem_3_1
-- name    : FiniteGroupTesting.LinearQuery.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:09:54.456194+00:00
-- url     : https://prove2.me/theorems/e12b0397-6236-49b6-aadd-a6037369b4b1
-- title:
--   Theorem 3.1 — sharper linear-query adaptive tester
-- statement:
--   There are positive fixed integers $A,B$ and a universal implementation constant $C>0$ such that, for every $n\ge4$ and $0<\epsilon<1/2$, the specified tester accepts every group with probability one, rejects every $\epsilon$-far operation with probability at least $2/3$, and on every input and random execution uses
--
--   $$Q\le10n+\lceil5/\bar\epsilon\rceil,\qquad T\le C\left(n\log n\log\log n+\frac{\log n}{\epsilon}\right),\qquad\bar\epsilon=\max\{\epsilon,n^{-2}\}.$$
--
--   The query numeral follows from at most $4n$ identity queries, less than $3n$ successful-extension queries and at most $3n$ for a final rejecting extension. Since $q\le5/\epsilon+1$, the query bound is at most $11(n+1/\epsilon)$. Both resource maxima include rejection and all preprocessing outcomes. The runtime constant and integer preprocessing choices precede all instances.
--
--   Differences from the source:
--   - encoding: [n] = {1,...,n} and its subsets → Fin n with i relabelled i+1, and indexed stored subsets; reason: bijections preserve every table entry, group, and probability; unused ambient labels are fixed by stored permutations
--   - reading: explicit-permutation constant-time lookup and real accuracy parameters → charged unit-cost randomized RAM semantics with exact uniform-interval sampling and one charged table-independent integer accuracy conversion; reason: the paper specifies no bit-machine or real-input representation; subsequent operations are finite-word array access, arithmetic, comparisons and loops
--   - encoding: O(log n) sampled labels and O(log n) word depth → fixed positive integers A,B give A ceil(log_2 n) samples and B ceil(log_2 n) depth; reason: A,B are chosen once to dominate Corollary 2.4 constants, before every input; extra generators and depth preserve success
--   - encoding: O(n+1/epsilon) query complexity → at most 10n+ceil(5/max(epsilon,n^(-2))) queries; reason: the proof gives 4n identity queries, less than 3n successful-extension queries and at most 3n for a final failed extension; q≤5/epsilon+1 yields the same order
--   - reading: there is a randomized adaptive tester running in the stated time → the specified program sectionTester A B (the Section 3.5 tester) satisfies the guarantees; reason: in the run semantics, transitions between charged nodes are arbitrary Lean functions, so an existential over programs would leave computation uncharged; fixing the paper's own algorithm gives the time bound content and implies the existential claim
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 15, proof p. 24, Theorem 3.1

import Definitions.Def_FiniteGroupTesting_LinearQuery_Tester

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery
open OracleRun

/-- Theorem 3.1, p. 15 (proof p. 24), with the safe proof-derived query numeral 10.
All implementation constants precede size, accuracy, oracle and every random execution. -/
theorem theorem_3_1 :
    ∃ A B : ℕ, ∃ C : ℝ, 0 < A ∧ 0 < B ∧ 0 < C ∧
      ∀ n : ℕ, 4 ≤ n → ∀ ε : ℝ, 0 < ε → ε < 1/2 →
        TestsGroups ε (sectionTester A B n ε) ∧
          ResourceBound (sectionTester A B n ε) (10 * n + (accuracyBudget n ε : ℝ))
            (C * ((n : ℝ) * Real.log n * Real.log (Real.log n) + Real.log n / ε)) := by sorry

end FiniteGroupTesting.LinearQuery
