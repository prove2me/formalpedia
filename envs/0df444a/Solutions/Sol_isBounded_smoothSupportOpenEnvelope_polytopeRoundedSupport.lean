-- Prove2me | solution 1 for isBounded_smoothSupportOpenEnvelope_polytopeRoundedSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:26:12.677859+00:00
-- url     : https://prove2.me/submissions/554c0401-76c6-4359-905f-54ff37c8563e

import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Theorems.Thm_isCompact_smoothSupportClosedEnvelope_polytopeRoundedSupport

set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace
theorem _root_.solution
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 ≤ rho) :
    Bornology.IsBounded
      (smoothSupportOpenEnvelope (polytopeRoundedSupport u delta rho)) := by
  exact
    (isCompact_smoothSupportClosedEnvelope_polytopeRoundedSupport
      hu hdelta hrho).isBounded.subset interior_subset
