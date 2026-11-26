-- Prove2me | solution 1 for nonempty_smoothSupportOpenEnvelope_polytopeRoundedSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:27:10.831105+00:00
-- url     : https://prove2.me/submissions/b6defd3c-1621-4f16-8667-84d4461b06a0

import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Theorems.Thm_convexHull_subset_smoothSupportOpenEnvelope_polytopeRoundedSupport


set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace
theorem _root_.solution
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) :
    (smoothSupportOpenEnvelope
      (polytopeRoundedSupport u delta rho)).Nonempty := by
  obtain ⟨z, hz⟩ := hu
  exact ⟨z,
    convexHull_subset_smoothSupportOpenEnvelope_polytopeRoundedSupport
      hdelta hrho ((subset_convexHull ℝ (u : Set ℂ)) hz)⟩
