-- Prove2me | solution 1 for deriv_smoothSupportCurve_projection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:12:28.931802+00:00
-- url     : https://prove2.me/submissions/c4ee7b88-b8f6-4d9b-9931-9ea4983557b1

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
import Theorems.Thm_polytopeDirectionalValue_smoothSupportCurve

set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff
theorem _root_.solution
    {h : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ h)
    (theta phi : ℝ) :
    deriv
      (fun x => polytopeDirectionalValue (smoothSupportCurve h x) theta) phi =
      smoothSupportCurvatureRadius h phi * Real.sin (theta - phi) := by
  have hh : DifferentiableAt ℝ h phi :=
    hsmooth.differentiable (by norm_num) phi
  have hderivSmooth : ContDiff ℝ ∞ (deriv h) :=
    (contDiff_infty_iff_deriv.mp hsmooth).2
  have hdh : DifferentiableAt ℝ (deriv h) phi :=
    hderivSmooth.differentiable (by norm_num) phi
  have hsub : DifferentiableAt ℝ (fun x : ℝ => theta - x) phi :=
    differentiableAt_const theta |>.sub differentiableAt_id
  have hcos : DifferentiableAt ℝ (fun x : ℝ => Real.cos (theta - x)) phi :=
    hsub.cos
  have hsin : DifferentiableAt ℝ (fun x : ℝ => Real.sin (theta - x)) phi :=
    hsub.sin
  have hsub_deriv : deriv (fun x : ℝ => theta - x) phi = -1 := by
    change deriv ((fun _ : ℝ => theta) - id) phi = _
    rw [deriv_sub (differentiableAt_const theta) differentiableAt_id,
      deriv_const, deriv_id]
    ring
  rw [show (fun x => polytopeDirectionalValue (smoothSupportCurve h x) theta) =
      (fun x => h x * Real.cos (theta - x) +
        deriv h x * Real.sin (theta - x)) by
    funext x
    exact polytopeDirectionalValue_smoothSupportCurve h theta x]
  change deriv
    (h * (fun x => Real.cos (theta - x)) +
      deriv h * (fun x => Real.sin (theta - x))) phi = _
  rw [deriv_add (hh.mul hcos) (hdh.mul hsin),
    deriv_mul hh hcos, deriv_mul hdh hsin,
    deriv_cos hsub, deriv_sin hsub, hsub_deriv]
  unfold smoothSupportCurvatureRadius
  ring
