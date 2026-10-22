-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_radial_derivative_ne_zero
-- name    : BirkhoffGlobalSection.convex_model_radial_derivative_ne_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T22:01:06.226403+00:00
-- url     : https://prove2.me/theorems/eb27ec98-3107-4ea6-9283-d205591f8425
-- title:
--   Convex model radial derivative ne zero
-- statement:
--   The convex model Hamiltonian radial derivative is nonzero at every boundary point.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Original auxiliary result from the accepted source Solutions/Sol_BirkhoffGlobalSection_convex_model_smooth_radial_chart.lean:7. Exact quantified statement retained; foundational calculus and geometry are imported from Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Theorems.Thm_ConvexAnalysis_convex_frontier_radial_derivative_ne_zero
import Theorems.Thm_BirkhoffGlobalSection_smooth_radial_gauge_chart

open BirkhoffGlobalSection ConvexAnalysis Filter Set
open scoped ContDiff Topology


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_radial_derivative_ne_zero {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) :
    ∀ y ∈ frontier M.body, fderiv ℝ M.modelHamiltonian y y ≠ 0 := by sorry
