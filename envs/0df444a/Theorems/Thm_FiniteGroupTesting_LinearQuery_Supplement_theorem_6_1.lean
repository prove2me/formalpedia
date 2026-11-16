-- Prove2me | Theorems.Thm_FiniteGroupTesting_LinearQuery_Supplement_theorem_6_1
-- name    : FiniteGroupTesting.LinearQuery.Supplement.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:27:03.024282+00:00
-- url     : https://prove2.me/theorems/2d73b2b0-d2f0-4593-aa95-826dd5b29af4
-- title:
--   Theorem 6.1 — Adaptive randomized two-sided lower-bound companion theorem
-- statement:
--   There are absolute constants $c,\epsilon_0>0$ and an infinite set of sizes $n$ such that, for every $n^{-2}\le\epsilon\le\epsilon_0$, every adaptive randomized two-sided $\epsilon$-tester for the group property has worst-case query bound $t$ satisfying
--   $$t\ge c\left(n^{1/5}+1/\epsilon\right).$$
--   Both constants are fixed before the infinite size family, accuracy and tester. Each selected size is at least three and has a nonempty accuracy interval. Randomization is an arbitrary probability distribution over the finite set of depth-$t$ adaptive query trees, so the statement includes arbitrary internal randomization and unrestricted offline computation. Both lower-bound terms are retained; there is no restriction to constant distance or nonadaptive algorithms.
--
--   Differences from the source:
--   - encoding: labels [n]={1,...,n} → Fin n with zero representing paper label 1; reason: bijective relabelling preserves all tables, distances and query policies
--   - encoding: every randomized adaptive tester with worst-case query bound t → every probability distribution on all deterministic depth-t adaptive ordered-pair query trees; reason: fixing randomness yields such a tree, and pushing forward any internal random law gives an arbitrary distribution on this finite set
--   - encoding: infinitely many sizes with the stated accuracy range → an infinite set S with n>=3 and n^(-2)<=epsilon_0 explicitly; reason: discarding finitely many small sizes preserves the source family and makes nonvacuity of every interval explicit
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 34–35, Theorem 6.1

import Definitions.Def_FiniteGroupTesting_LinearQuery_Supplement_TranscriptModel

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery.Supplement

theorem theorem_6_1 :
    ∃ c ε₀ : ℝ, 0 < c ∧ 0 < ε₀ ∧ ∃ S : Set ℕ, S.Infinite ∧
      ∀ n ∈ S, 3 ≤ n ∧ (n : ℝ)⁻¹ ^ 2 ≤ ε₀ ∧
        ∀ ε : ℝ, (n : ℝ)⁻¹ ^ 2 ≤ ε → ε ≤ ε₀ →
          ∀ t : ℕ, ∀ μ : PMF (QueryTree n t), RandomizedTester ε μ →
            c * ((n : ℝ) ^ (1/5 : ℝ) + 1 / ε) ≤ t := by sorry

end FiniteGroupTesting.LinearQuery.Supplement
