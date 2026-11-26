-- Prove2me | solution 1 for exists_pos_mul_polytopeDirectionalValue_eq_realContinuousLinearMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:34:16.602854+00:00
-- url     : https://prove2.me/submissions/bd12b9a1-771c-49dd-b950-7be5e2118b86

import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_Operator_Crouzeix_PlanarDualDirection
import Theorems.Thm_realContinuousLinearMap_apply_eq_re_im
import Theorems.Thm_realContinuousLinearMapCoefficient_re
import Theorems.Thm_realContinuousLinearMapCoefficient_im
import Theorems.Thm_realContinuousLinearMapCoefficient_ne_zero
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


attribute [local simp] realContinuousLinearMapCoefficient_re
attribute [local simp] realContinuousLinearMapCoefficient_im

set_option autoImplicit false
open Complex
theorem _root_.solution
    {f : ℂ →L[ℝ] ℝ} (hf : f ≠ 0) :
    ∃ c theta : ℝ, 0 < c ∧
      ∀ z : ℂ, c * polytopeDirectionalValue z theta = f z := by
  let q : ℂ := realContinuousLinearMapCoefficient f
  let c : ℝ := ‖q‖
  let theta : ℝ := q.arg
  have hq : q ≠ 0 := realContinuousLinearMapCoefficient_ne_zero hf
  have hc : 0 < c := by
    dsimp only [c]
    exact norm_pos_iff.mpr hq
  refine ⟨c, theta, hc, ?_⟩
  intro z
  unfold polytopeDirectionalValue
  calc
    c * (z.re * Real.cos theta + z.im * Real.sin theta) =
        z.re * (‖q‖ * Real.cos q.arg) +
          z.im * (‖q‖ * Real.sin q.arg) := by
      dsimp only [c, theta]
      ring
    _ = z.re * q.re + z.im * q.im := by
      rw [Complex.norm_mul_cos_arg, Complex.norm_mul_sin_arg]
    _ = z.re * f 1 + z.im * f I := by
      rw [show q.re = f 1 by rfl, show q.im = f I by rfl]
    _ = f z := (realContinuousLinearMap_apply_eq_re_im f z).symm
