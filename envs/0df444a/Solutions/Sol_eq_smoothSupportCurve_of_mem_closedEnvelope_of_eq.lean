-- Prove2me | solution 1 for eq_smoothSupportCurve_of_mem_closedEnvelope_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:30:20.800227+00:00
-- url     : https://prove2.me/submissions/1286386a-f023-487f-9e7f-bb5f9a62f49e

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveRange
import Theorems.Thm_deriv_polytopeDirectionalValue_right
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_hasMergelyanPolynomialApproximation_iff
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_boundaryParam
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_hasMergelyanPolynomialApproximation_iff
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_boundaryParam
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_boundaryParam_deriv
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_boundaryParam_outwardNormal
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_carrier
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_closure_carrier
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_frontier_carrier
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_smoothSupportDirectionalLinearMap_apply
attribute [local simp] SmoothJordanDomain.canonicalOrientation_carrier
attribute [local simp] SmoothJordanDomain.canonicalOrientation_hasMergelyanPolynomialApproximation_iff
attribute [local simp] SmoothJordanDomain.reverseOrientation_boundaryParam
attribute [local simp] SmoothJordanDomain.reverseOrientation_carrier
attribute [local simp] SmoothJordanDomain.reverseOrientation_hasMergelyanPolynomialApproximation_iff
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_boundaryParam
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_boundaryParam_deriv
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_boundaryParam_outwardNormal
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_carrier
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_closure_carrier
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_frontier_carrier
attribute [local simp] crouzeixPolynomialBoundaryPhaseTransform_zero
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange
attribute [local simp] smoothSupportDirectionalLinearMap_apply



set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff
theorem _root_.solution
    {h : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ h)
    {z : ℂ} (hz : z ∈ smoothSupportClosedEnvelope h) {theta : ℝ}
    (hactive : polytopeDirectionalValue z theta = h theta) :
    z = smoothSupportCurve h theta := by
  let gap : ℝ → ℝ := fun x => polytopeDirectionalValue z x - h x
  have hmax : IsLocalMax gap theta := by
    apply Filter.Eventually.of_forall
    intro x
    dsimp only [gap]
    have hx := hz x
    linarith
  have hgapDeriv : deriv gap theta =
      (-z.re * Real.sin theta + z.im * Real.cos theta) - deriv h theta := by
    dsimp only [gap]
    change deriv (polytopeDirectionalValue z - h) theta = _
    have hdirDiff : DifferentiableAt ℝ (polytopeDirectionalValue z) theta := by
      unfold polytopeDirectionalValue
      fun_prop
    rw [deriv_sub
      hdirDiff
      (hsmooth.differentiable (by norm_num) theta),
      deriv_polytopeDirectionalValue_right]
  have htangent :
      -z.re * Real.sin theta + z.im * Real.cos theta = deriv h theta := by
    have hzero := hmax.deriv_eq_zero
    rw [hgapDeriv] at hzero
    linarith
  rw [show smoothSupportCurve h theta =
      h theta • smoothSupportUnitNormal theta +
        deriv h theta • smoothSupportUnitTangent theta by rfl]
  unfold polytopeDirectionalValue at hactive
  have hre : z.re =
      h theta * Real.cos theta - deriv h theta * Real.sin theta := by
    calc
      z.re = z.re * (Real.sin theta ^ 2 + Real.cos theta ^ 2) := by
        rw [Real.sin_sq_add_cos_sq, mul_one]
      _ =
          (z.re * Real.cos theta + z.im * Real.sin theta) *
              Real.cos theta -
            (-z.re * Real.sin theta + z.im * Real.cos theta) *
              Real.sin theta := by
        ring
      _ = h theta * Real.cos theta - deriv h theta * Real.sin theta := by
        rw [hactive, htangent]
  have him : z.im =
      h theta * Real.sin theta + deriv h theta * Real.cos theta := by
    calc
      z.im = z.im * (Real.sin theta ^ 2 + Real.cos theta ^ 2) := by
        rw [Real.sin_sq_add_cos_sq, mul_one]
      _ =
          (z.re * Real.cos theta + z.im * Real.sin theta) *
              Real.sin theta +
            (-z.re * Real.sin theta + z.im * Real.cos theta) *
              Real.cos theta := by
        ring
      _ = h theta * Real.sin theta + deriv h theta * Real.cos theta := by
        rw [hactive, htangent]
  apply Complex.ext
  · unfold smoothSupportUnitTangent smoothSupportUnitNormal
    simp only [Complex.add_re, Complex.smul_re, Complex.mul_re,
      circleMap_zero_re, circleMap_zero_im, I_re, I_im, one_mul,
      mul_zero, mul_one, zero_sub, smul_eq_mul]
    simpa only [sub_eq_add_neg, mul_neg] using hre
  · unfold smoothSupportUnitTangent smoothSupportUnitNormal
    simp only [Complex.add_im, Complex.smul_im, Complex.mul_im,
      circleMap_zero_re, circleMap_zero_im, I_re, I_im, one_mul,
      mul_zero, mul_one, smul_eq_mul]
    simpa only [add_zero] using him
