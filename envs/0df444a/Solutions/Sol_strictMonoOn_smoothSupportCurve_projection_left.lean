-- Prove2me | solution 1 for strictMonoOn_smoothSupportCurve_projection_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:15:58.887918+00:00
-- url     : https://prove2.me/submissions/492f8c29-92f3-405f-ac85-21d9e949c66f

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
import Theorems.Thm_deriv_smoothSupportCurve_projection
import Theorems.Thm_hasDerivAt_smoothSupportCurve_projection
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
    (hcurv : ∀ x, 0 < smoothSupportCurvatureRadius h x)
    (theta : ℝ) :
    StrictMonoOn
      (fun x => polytopeDirectionalValue (smoothSupportCurve h x) theta)
      (Icc (theta - Real.pi) theta) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc (theta - Real.pi) theta)
  · exact (continuous_iff_continuousAt.2 fun x =>
      (hasDerivAt_smoothSupportCurve_projection hsmooth theta x).continuousAt).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    simp only [mem_Ioo] at hx
    rw [deriv_smoothSupportCurve_projection hsmooth]
    exact mul_pos (hcurv x)
      (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
