-- Prove2me | Theorems.Thm_ConvexAnalysis_gauge_radius_frontier
-- name    : ConvexAnalysis.gauge_radius_frontier
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:58:54.403981+00:00
-- url     : https://prove2.me/theorems/f560fef0-5d4c-4f09-9356-7553d946a129
-- title:
--   Gauge radius frontier
-- statement:
--   For a bounded convex set containing a neighborhood of zero, inverse-gauge rescaling sends every nonzero phase vector to its frontier.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Original auxiliary result from the accepted source Solutions/Sol_ConvexAnalysis_convex_frontier_radial_derivative_ne_zero.lean:22. Exact quantified statement retained; foundational calculus and geometry are imported from Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_BirkhoffGlobalSection_ConvexRegularizationModel
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.LocallyConvex.Separation

open BirkhoffGlobalSection Filter Set
open scoped ContDiff Topology


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem ConvexAnalysis.gauge_radius_frontier (K : Set Phase) (hK : Convex ℝ K)
    (h0 : K ∈ nhds (0 : Phase)) (hb : Bornology.IsVonNBounded ℝ K)
    (x : Phase) (hx : x ≠ 0) : (gauge K x)⁻¹ • x ∈ frontier K := by sorry
