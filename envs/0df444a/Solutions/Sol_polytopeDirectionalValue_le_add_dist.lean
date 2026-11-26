-- Prove2me | solution 1 for polytopeDirectionalValue_le_add_dist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:09:15.364134+00:00
-- url     : https://prove2.me/submissions/8f2ad820-468d-4437-96be-28d7916806bd

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
import Theorems.Thm_smoothSupportDirectionalLinearMap_apply
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
open scoped ComplexConjugate
theorem _root_.solution
    (z w : ℂ) (theta : ℝ) :
    polytopeDirectionalValue w theta ≤
      polytopeDirectionalValue z theta + dist w z := by
  let n : ℂ := circleMap 0 1 theta
  have hid (v : ℂ) :
      polytopeDirectionalValue v theta = (conj n * v).re := by
    unfold polytopeDirectionalValue n
    simp only [circleMap_zero_re, circleMap_zero_im, one_mul,
      Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  calc
    polytopeDirectionalValue w theta =
        polytopeDirectionalValue z theta +
          (conj n * (w - z)).re := by
      rw [hid w, hid z]
      simp only [mul_sub, Complex.sub_re]
      ring
    _ ≤ polytopeDirectionalValue z theta +
        ‖conj n * (w - z)‖ := by
      simpa only [add_comm] using
        add_le_add_left (Complex.re_le_norm (conj n * (w - z)))
          (polytopeDirectionalValue z theta)
    _ = polytopeDirectionalValue z theta + dist w z := by
      rw [norm_mul, Complex.norm_conj, show ‖n‖ = 1 by
        unfold n
        rw [norm_circleMap_zero, abs_one], one_mul, dist_eq_norm]
