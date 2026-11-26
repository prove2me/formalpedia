-- Prove2me | solution 1 for smoothSupportCurve_not_mem_smoothSupportOpenEnvelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:29:56.940485+00:00
-- url     : https://prove2.me/submissions/bb036405-d879-4a09-ad9f-8374d44230c5

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
import Theorems.Thm_polytopeDirectionalValue_smoothSupportUnitNormal_self
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
import Theorems.Thm_isOpen_smoothSupportOpenEnvelope
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_polytopeDirectionalValue_smoothSupportCurve_self
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
    (h : ℝ → ℝ) (theta : ℝ) :
    smoothSupportCurve h theta ∉ smoothSupportOpenEnvelope h := by
  intro hz
  obtain ⟨eps, heps, hepsSub⟩ :=
    Metric.isOpen_iff.mp (isOpen_smoothSupportOpenEnvelope h)
      (smoothSupportCurve h theta) hz
  let w : ℂ := smoothSupportCurve h theta +
    (eps / 2) • smoothSupportUnitNormal theta
  have hwball : w ∈ ball (smoothSupportCurve h theta) eps := by
    rw [mem_ball, dist_eq_norm]
    dsimp only [w]
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    unfold smoothSupportUnitNormal
    rw [norm_circleMap_zero, abs_one, mul_one]
    linarith
  have hwclosed : w ∈ smoothSupportClosedEnvelope h :=
    interior_subset (hepsSub hwball)
  have hwdir := hwclosed theta
  have hself := polytopeDirectionalValue_smoothSupportCurve_self h theta
  have hwdirEq : polytopeDirectionalValue w theta = h theta + eps / 2 := by
    dsimp only [w]
    rw [← smoothSupportDirectionalLinearMap_apply,
      map_add, map_smul, smoothSupportDirectionalLinearMap_apply,
      smoothSupportDirectionalLinearMap_apply,
      polytopeDirectionalValue_smoothSupportUnitNormal_self,
      hself]
    simp only [smul_eq_mul, mul_one]
  rw [hwdirEq] at hwdir
  linarith
