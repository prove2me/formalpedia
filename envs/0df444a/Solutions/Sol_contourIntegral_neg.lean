-- Prove2me | solution 1 for contourIntegral_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:02:08.6244+00:00
-- url     : https://prove2.me/submissions/903a7e85-bf0c-46a3-93fd-c801f44db873

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Definitions.Def_Operator_Crouzeix_ContourIntegral

set_option autoImplicit false
open scoped Real Interval
open MeasureTheory Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
theorem _root_.solution (f : ℂ → F) (γ : ℝ → ℂ) :
    contourIntegral (fun z => -f z) γ = -contourIntegral f γ := by
  unfold contourIntegral
  simp only [smul_neg]
  exact intervalIntegral.integral_neg
