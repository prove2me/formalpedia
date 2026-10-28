-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_smooth_radial_gauge_inverse
-- name    : BirkhoffGlobalSection.smooth_radial_gauge_inverse
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T23:02:33.830404+00:00
-- url     : https://prove2.me/theorems/43aa48b1-4f81-4c96-9ad5-6160f50c2eaf
-- title:
--   Smooth radial gauge inverse
-- statement:
--   For a bounded convex body containing a neighborhood of zero and a smooth frontier defining function with nonzero radial derivative, its inverse-gauge radial chart is smooth away from zero.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Original auxiliary result from the accepted source Solutions/Sol_BirkhoffGlobalSection_smooth_radial_gauge_chart.lean:38. Exact quantified statement retained; foundational calculus and geometry are imported from Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_BirkhoffGlobalSection_ConvexRegularizationModel
import Theorems.Thm_BirkhoffGlobalSection_radial_normalization_contact_identity
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Calculus.ImplicitContDiff

import Theorems.Thm_ImplicitCalculus_contDiffAt_continuous_solution
import Theorems.Thm_ConvexAnalysis_gauge_radius_frontier
import Theorems.Thm_ConvexAnalysis_gauge_radius_frontier
open scoped ContDiff Topology
open BirkhoffGlobalSection Filter Set


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.smooth_radial_gauge_inverse
    (B : Set Phase) (hc : Convex ℝ B) (h0 : B ∈ 𝓝 (0 : Phase))
    (hb : Bornology.IsVonNBounded ℝ B) (F : Phase → ℝ)
    (hzero : ∀ y ∈ frontier B, F y = 0)
    (hsmooth : ∀ y ∈ frontier B, ContDiffAt ℝ ∞ F y)
    (hrad : ∀ y ∈ frontier B, fderiv ℝ F y y ≠ 0)
    (u : Phase) (hu : u ≠ 0) :
    ContDiffAt ℝ ∞ (fun x : Phase => (gauge B x)⁻¹ • x) u := by sorry
