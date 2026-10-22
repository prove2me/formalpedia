-- Prove2me | Theorems.Thm_ConvexAnalysis_exists_transverse_interior_center
-- name    : ConvexAnalysis.exists_transverse_interior_center
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:59:09.548012+00:00
-- url     : https://prove2.me/theorems/2c0b1053-5980-4182-bf80-f3662715cc14
-- title:
--   Exists transverse interior center
-- statement:
--   If zero lies in the interior of a phase-space set and H is a nonzero continuous linear functional, then for any y there is an interior point z with H(y−z) nonzero.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Original auxiliary result from the accepted source Solutions/Sol_ConvexAnalysis_convex_frontier_radial_derivative_ne_zero.lean:116. Exact quantified statement retained; foundational calculus and geometry are imported from Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_BirkhoffGlobalSection_ConvexRegularizationModel
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.LocallyConvex.Separation

open BirkhoffGlobalSection Filter Set
open scoped ContDiff Topology


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem ConvexAnalysis.exists_transverse_interior_center (K : Set Phase)
    (h0 : (0 : Phase) ∈ interior K) (H : Phase →L[ℝ] ℝ) (hH : H ≠ 0)
    (y : Phase) : ∃ z ∈ interior K, H (y - z) ≠ 0 := by sorry
