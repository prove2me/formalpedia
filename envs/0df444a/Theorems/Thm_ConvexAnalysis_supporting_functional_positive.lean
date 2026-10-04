-- Prove2me | Theorems.Thm_ConvexAnalysis_supporting_functional_positive
-- name    : ConvexAnalysis.supporting_functional_positive
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T18:40:24.496271+00:00
-- url     : https://prove2.me/theorems/b6961aea-8beb-4ab2-9e98-2b76357dfe8a
-- title:
--   Strict positivity of a nonzero supporting functional
-- statement:
--   Let K be a subset of a real normed vector space with zero in its interior. If a nonzero continuous linear functional L is bounded above on K by L(y), then L(y) is strictly positive. Convexity of K and membership of y in K are not required.
-- source:
--   Original auxiliary result generalized from Solutions/Sol_ConvexAnalysis_convex_frontier_radial_derivative_ne_zero.lean:10. Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Analysis/Calculus/LocalExtr/Basic.lean; Analysis/Calculus/ContDiff/Deriv.lean; Analysis/Calculus/Deriv/Mul.lean. https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Calculus. No claim of a separate article theorem.

import Mathlib.Analysis.Calculus.LocalExtr.Basic
open Set Filter
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem ConvexAnalysis.supporting_functional_positive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (K : Set E)
    (h0 : (0 : E) ∈ interior K) (L : E →L[ℝ] ℝ) (hL : L ≠ 0)
    (y : E) (hsupport : ∀ x ∈ K, L x ≤ L y) : 0 < L y := by sorry
