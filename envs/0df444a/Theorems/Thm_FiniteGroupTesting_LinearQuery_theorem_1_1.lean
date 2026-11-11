-- Prove2me | Theorems.Thm_FiniteGroupTesting_LinearQuery_theorem_1_1
-- name    : FiniteGroupTesting.LinearQuery.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:09:59.766996+00:00
-- url     : https://prove2.me/theorems/7c4a13cc-e487-410a-b29c-dc793adccf51
-- title:
--   Theorem 1.1 — one-sided linear-query group testing
-- statement:
--   There are fixed positive preprocessing integers $A,B$ and a universal $C>0$ such that, for every positive finite size $n$ and every real $\epsilon>0$, one specified adaptive tester accepts every group with probability one and rejects every $\epsilon$-far operation with probability at least $2/3$. Every input and every random execution obey
--
--   $$Q\le20(n+1/\epsilon),\qquad T\le C(n+1/\epsilon)\left(1+\left\lceil\log_2(2n+2/\epsilon)\right\rceil\right)^2.$$
--
--   Thus the query order is $O(n+1/\epsilon)$ and charged running time is $\widetilde O(n+1/\epsilon)$, with uniform exponent two. For $n\le3$ the complete table is checked exactly; for $\epsilon\ge1/2$ the core uses accuracy $1/4$. Otherwise it uses $\bar\epsilon=\max\{\epsilon,n^{-2}\}$ and $q=\lceil5/\bar\epsilon\rceil$. The wrapper query constant 20 covers both the core and these branches. No identity, inverse, regularity, candidate group law or correctness promise is input to the tester.
--
--   Differences from the source:
--   - encoding: [n] = {1,...,n} and its subsets → Fin n with i relabelled i+1, and indexed stored subsets; reason: bijections preserve every table entry, group, and probability; unused ambient labels are fixed by stored permutations
--   - reading: explicit-permutation constant-time lookup and real accuracy parameters → charged unit-cost randomized RAM semantics with exact uniform-interval sampling and one charged table-independent integer accuracy conversion; reason: the paper specifies no bit-machine or real-input representation; subsequent operations are finite-word array access, arithmetic, comparisons and loops
--   - encoding: O(log n) sampled labels and O(log n) word depth → fixed positive integers A,B give A ceil(log_2 n) samples and B ceil(log_2 n) depth; reason: A,B are chosen once to dominate Corollary 2.4 constants, before every input; extra generators and depth preserve success
--   - encoding: one-sided tester over the headline full testing domain → exact verification for n≤3 and the 1/4 core branch when epsilon≥1/2; reason: bounded-size exact verification costs at most 3n queries; epsilon-far for epsilon≥1/2 implies 1/4-far, preserving the full domain
--   - encoding: O(n+1/epsilon) queries and soft-O(n+1/epsilon) time → 20(n+1/epsilon) queries and C(n+1/epsilon)(1+ceil(log_2(2n+2/epsilon)))^2 time; reason: safe proof-derived query constants and a uniform exponent-two envelope instantiate exactly the source orders
--   - reading: there is a randomized adaptive tester running in the stated time → the specified program headlineTester A B (exact check for n≤3, otherwise the Section 3 tester) satisfies the guarantees; reason: in the run semantics, transitions between charged nodes are arbitrary Lean functions, so an existential over programs would leave computation uncharged; fixing the paper's own algorithm gives the time bound content and implies the existential claim
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 2, Theorem 1.1; implementation §§3.3–3.5, pp. 22–24

import Definitions.Def_FiniteGroupTesting_LinearQuery_Tester

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery
open OracleRun

/-- Theorem 1.1, p. 2: every positive size and every positive accuracy, perfect completeness, soundness,
worst-case linear queries and soft-linear charged time, with a uniform exponent of two. -/
theorem theorem_1_1 :
    ∃ A B : ℕ, ∃ C : ℝ, 0 < A ∧ 0 < B ∧ 0 < C ∧
      ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε →
        TestsGroups ε (headlineTester A B n ε) ∧
          ResourceBound (headlineTester A B n ε) (20 * ((n : ℝ) + 1 / ε))
            (C * ((n : ℝ) + 1 / ε) *
              (1 + (⌈Real.logb 2 (2 * n + 2 / ε)⌉₊ : ℝ)) ^ 2) := by sorry

end FiniteGroupTesting.LinearQuery
