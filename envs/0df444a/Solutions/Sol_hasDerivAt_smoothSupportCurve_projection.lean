-- Prove2me | solution 1 for hasDerivAt_smoothSupportCurve_projection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:14:32.241283+00:00
-- url     : https://prove2.me/submissions/0bdb4a9c-b21d-4136-8d14-93bc61d965a0

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
import Theorems.Thm_polytopeDirectionalValue_smoothSupportCurve
import Theorems.Thm_deriv_smoothSupportCurve_projection

set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff
theorem _root_.solution
    {h : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ h)
    (theta phi : ℝ) :
    HasDerivAt
      (fun x => polytopeDirectionalValue (smoothSupportCurve h x) theta)
      (smoothSupportCurvatureRadius h phi * Real.sin (theta - phi)) phi := by
  have hdiff : DifferentiableAt ℝ
      (fun x => polytopeDirectionalValue (smoothSupportCurve h x) theta) phi := by
    rw [show (fun x => polytopeDirectionalValue (smoothSupportCurve h x) theta) =
        (fun x => h x * Real.cos (theta - x) +
          deriv h x * Real.sin (theta - x)) by
      funext x
      exact polytopeDirectionalValue_smoothSupportCurve h theta x]
    have hh := hsmooth.differentiable (by norm_num) phi
    have hdh := ((contDiff_infty_iff_deriv.mp hsmooth).2.differentiable
      (by norm_num) phi)
    have hsub : DifferentiableAt ℝ (fun x : ℝ => theta - x) phi :=
      differentiableAt_const theta |>.sub differentiableAt_id
    exact (hh.mul hsub.cos).add (hdh.mul hsub.sin)
  have hd := hdiff.hasDerivAt
  rwa [deriv_smoothSupportCurve_projection hsmooth theta phi] at hd
