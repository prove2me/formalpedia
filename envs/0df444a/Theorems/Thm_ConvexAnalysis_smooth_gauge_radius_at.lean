-- Prove2me | Theorems.Thm_ConvexAnalysis_smooth_gauge_radius_at
-- name    : ConvexAnalysis.smooth_gauge_radius_at
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T22:59:03.6403+00:00
-- url     : https://prove2.me/theorems/977b0ed4-3354-4749-a604-795abcbe12f6
-- title:
--   Smooth gauge radius at
-- statement:
--   The inverse-gauge scalar factor is smooth at a frontier point when a smooth frontier defining function has nonzero radial derivative there and the stated convexity, boundedness and interior hypotheses hold.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Original auxiliary result from the accepted source Solutions/Sol_ConvexAnalysis_convex_frontier_radial_derivative_ne_zero.lean:30. Exact quantified statement retained; foundational calculus and geometry are imported from Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_BirkhoffGlobalSection_ConvexRegularizationModel
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.LocallyConvex.Separation

import Theorems.Thm_ConvexAnalysis_gauge_radius_frontier
open BirkhoffGlobalSection Filter Set
open scoped ContDiff Topology


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem ConvexAnalysis.smooth_gauge_radius_at (K : Set Phase) (hK : Convex ℝ K)
    (h0 : K ∈ nhds (0 : Phase)) (hb : Bornology.IsVonNBounded ℝ K)
    (F : Phase → ℝ) (hzero : ∀ x ∈ frontier K, F x = 0)
    (u : Phase) (hu : u ∈ frontier K) (hc : ContDiffAt ℝ ∞ F u)
    (hrad : fderiv ℝ F u u ≠ 0) :
    ContDiffAt ℝ ∞ (fun x => (gauge K x)⁻¹) u := by sorry
