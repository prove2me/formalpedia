-- Prove2me | Theorems.Thm_ConvexAnalysis_convex_frontier_radial_derivative_ne_zero
-- name    : ConvexAnalysis.convex_frontier_radial_derivative_ne_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-02T00:09:26.611969+00:00
-- url     : https://prove2.me/theorems/760bd7e2-ccfc-4d04-bf8c-af6a1bd50ccd
-- title:
--   A regular smooth convex frontier has nonzero radial derivative
-- statement:
--   Let K be a compact convex body in real four-dimensional phase space, with the origin in its interior. Let F vanish on the frontier of K, and let y lie on that frontier. If F is smooth at y and DF_y is nonzero, then
--
--   $$DF_y(y)\ne0.$$
--
--   No inward sign or tangential Hessian condition is assumed. Only smoothness and regularity at the selected boundary point are required.
-- source:
--   Original auxiliary convex-boundary derivation in real four-dimensional Phase, using Mathlib Hahn--Banach separation (Analysis/LocallyConvex/Separation.lean), local extrema, gauge and implicit-function lemmas at revision 0df444a360eaa60ab8c11dca51a86af692955474, https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis. The local inverse-gauge argument adapts the accepted BirkhoffGlobalSection.smooth_radial_gauge_chart proof (cac241c3-aed1-4423-b740-7f890823f4e8). This is an auxiliary derivation, not a verbatim theorem of Joung--van Koert or Hryniewicz.

import Definitions.Def_BirkhoffGlobalSection_ConvexRegularizationModel
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.LocallyConvex.Separation

open BirkhoffGlobalSection Filter Set
open scoped ContDiff Topology

theorem ConvexAnalysis.convex_frontier_radial_derivative_ne_zero (K : Set Phase)
    (hcompact : IsCompact K) (hK : Convex ℝ K) (h0 : (0 : Phase) ∈ interior K)
    (F : Phase → ℝ) (hzero : ∀ x ∈ frontier K, F x = 0)
    (y : Phase) (hy : y ∈ frontier K) (hc : ContDiffAt ℝ ∞ F y)
    (hregular : fderiv ℝ F y ≠ 0) : fderiv ℝ F y y ≠ 0 := by sorry
