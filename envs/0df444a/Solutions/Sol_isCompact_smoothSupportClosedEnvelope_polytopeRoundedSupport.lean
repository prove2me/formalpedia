-- Prove2me | solution 1 for isCompact_smoothSupportClosedEnvelope_polytopeRoundedSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:29:24.395072+00:00
-- url     : https://prove2.me/submissions/b3373c2f-347d-4161-9ce4-0989e3229fb7

import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Theorems.Thm_smoothSupportClosedEnvelope_polytopeRoundedSupport_subset_cthickening
import Theorems.Thm_isClosed_smoothSupportClosedEnvelope


set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace
theorem _root_.solution
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 ≤ rho) :
    IsCompact
      (smoothSupportClosedEnvelope (polytopeRoundedSupport u delta rho)) := by
  have htarget : IsCompact
      (Metric.cthickening
        (delta * Real.log (u.card : ℝ) + rho)
        (convexHull ℝ (u : Set ℂ))) :=
    (u.finite_toSet.isCompact_convexHull ℝ).cthickening
  exact htarget.of_isClosed_subset
    (isClosed_smoothSupportClosedEnvelope _)
    (smoothSupportClosedEnvelope_polytopeRoundedSupport_subset_cthickening
      hu hdelta hrho)
