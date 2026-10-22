-- Prove2me | Theorems.Thm_ConvexAnalysis_convex_frontier_radial_derivative_positive
-- name    : ConvexAnalysis.convex_frontier_radial_derivative_positive
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-02T00:23:47.508284+00:00
-- url     : https://prove2.me/theorems/f232f561-18b5-434d-b4c6-07e2798ebefb
-- title:
--   Positive tangential curvature fixes the outward Hamiltonian sign
-- statement:
--   Let K be a compact convex body in real four-dimensional phase space, with the origin interior. Let F vanish on its frontier and be smooth and regular at a frontier point y. If its Hessian is positive on every nonzero vector v with DF_y(v)=0, then
--
--   $$DF_y(y)>0.$$
--
--   No inward-negativity or contact-positivity hypothesis is required. The second derivative is the directional derivative of x maps to DF_x(v), evaluated on v at y.
-- source:
--   Original auxiliary convex-boundary derivation in real four-dimensional Phase, using Mathlib Hahn--Banach separation (Analysis/LocallyConvex/Separation.lean), local extrema, gauge and implicit-function lemmas at revision 0df444a360eaa60ab8c11dca51a86af692955474, https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis. The local inverse-gauge argument adapts the accepted BirkhoffGlobalSection.smooth_radial_gauge_chart proof (cac241c3-aed1-4423-b740-7f890823f4e8). This is an auxiliary derivation, not a verbatim theorem of Joung--van Koert or Hryniewicz.

import Definitions.Def_BirkhoffGlobalSection_ConvexRegularizationModel

open BirkhoffGlobalSection Filter Set
open scoped ContDiff Topology

theorem ConvexAnalysis.convex_frontier_radial_derivative_positive (K : Set Phase)
    (hcompact : IsCompact K) (hK : Convex ℝ K) (h0 : (0 : Phase) ∈ interior K)
    (F : Phase → ℝ) (hzero : ∀ x ∈ frontier K, F x = 0)
    (y : Phase) (hy : y ∈ frontier K) (hc : ContDiffAt ℝ ∞ F y)
    (hregular : fderiv ℝ F y ≠ 0)
    (hcurv : ∀ v : Phase, v ≠ 0 → fderiv ℝ F y v = 0 →
      0 < fderiv ℝ (fun x => fderiv ℝ F x v) y v) : 0 < fderiv ℝ F y y := by sorry
