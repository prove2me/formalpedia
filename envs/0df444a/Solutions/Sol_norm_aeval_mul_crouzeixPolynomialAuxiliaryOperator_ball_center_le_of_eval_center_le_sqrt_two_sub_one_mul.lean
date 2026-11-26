-- Prove2me | solution 1 for norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_eval_center_le_sqrt_two_sub_one_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:32:30.357803+00:00
-- url     : https://prove2.me/submissions/91f26216-3281-4e59-8716-e93ad36a9ed2

import Definitions.Def_Operator_Crouzeix_ConvexRunge
import Definitions.Def_Operator_Crouzeix_NormalProduct
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_NumericalRange_Convex
import Definitions.Def_Operator_NumericalRange_Nonempty
import Definitions.Def_Operator_Crouzeix_NormalProductSymmetrized
import Theorems.Thm_Polynomial_aeval_affineComposition
import Theorems.Thm_Polynomial_eval_affineComposition
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
import Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_polynomialSupNorm_nonneg
import Theorems.Thm_polytopeRoundedSupportDomainOfRange_carrier
import Theorems.Thm_polytopeRoundedSupportDomain_boundaryParam
import Theorems.Thm_polytopeRoundedSupportDomain_carrier
import Theorems.Thm_smoothSupportDirectionalLinearMap_apply
attribute [local simp] Polynomial.aeval_affineComposition
attribute [local simp] Polynomial.eval_affineComposition
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
attribute [local simp] polytopeRoundedSupportDomainOfRange_carrier
attribute [local simp] polytopeRoundedSupportDomain_boundaryParam
attribute [local simp] polytopeRoundedSupportDomain_carrier
attribute [local simp] smoothSupportDirectionalLinearMap_apply



set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Pointwise
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    {K : Set ℂ} (p : Polynomial ℂ)
    (hsymm :
      ‖Polynomial.aeval A p +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) p)‖ ≤
        2 * polynomialSupNorm p K)
    (hsmall : ‖Polynomial.eval c p‖ ≤
      (Real.sqrt 2 - 1) * polynomialSupNorm p K) :
    ‖Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R
            ((norm_nonneg (A - c • 1)).trans_lt hA)) p‖ ≤
      polynomialSupNorm p K ^ 2 := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    have hzero : Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R
            ((norm_nonneg (A - c • 1)).trans_lt hA)) p = 0 :=
      Subsingleton.elim _ _
    rw [hzero, norm_zero]
    exact sq_nonneg _
  let _ := hE
  let m : ℝ := polynomialSupNorm p K
  let a : ℝ := ‖Polynomial.eval c p‖
  have hm : 0 ≤ m := polynomialSupNorm_nonneg p K
  have ha : 0 ≤ a := norm_nonneg _
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hk : 2 * (Real.sqrt 2 - 1) + (Real.sqrt 2 - 1) ^ 2 = 1 := by
    nlinarith only [hsqrt]
  have hsym := hsymm
  rw [crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
    A c hA p, star_smul, star_one, star_star] at hsym
  have hpA : ‖Polynomial.aeval A p‖ ≤ 2 * m + a := by
    calc
      ‖Polynomial.aeval A p‖ =
          ‖(Polynomial.aeval A p +
            Polynomial.eval c p • (1 : E →L[ℂ] E)) -
              Polynomial.eval c p • (1 : E →L[ℂ] E)‖ := by
            rw [add_sub_cancel_right]
      _ ≤ ‖Polynomial.aeval A p +
            Polynomial.eval c p • (1 : E →L[ℂ] E)‖ +
          ‖Polynomial.eval c p • (1 : E →L[ℂ] E)‖ := norm_sub_le _ _
      _ ≤ 2 * m + a := by
        rw [norm_smul, norm_one, mul_one]
        simpa only [m, a] using add_le_add hsym (le_refl a)
  have hlinear : 2 * m * a ≤
      2 * m * ((Real.sqrt 2 - 1) * m) :=
    mul_le_mul_of_nonneg_left hsmall (mul_nonneg (by norm_num) hm)
  have hsquare : a ^ 2 ≤ ((Real.sqrt 2 - 1) * m) ^ 2 :=
    pow_le_pow_left₀ ha hsmall 2
  have hfactor : (2 * m + a) * a ≤ m ^ 2 := by
    calc
      (2 * m + a) * a = 2 * m * a + a ^ 2 := by ring
      _ ≤ 2 * m * ((Real.sqrt 2 - 1) * m) +
          ((Real.sqrt 2 - 1) * m) ^ 2 := add_le_add hlinear hsquare
      _ = (2 * (Real.sqrt 2 - 1) + (Real.sqrt 2 - 1) ^ 2) * m ^ 2 := by ring
      _ = m ^ 2 := by rw [hk, one_mul]
  rw [crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
    A c hA p]
  calc
    ‖Polynomial.aeval A p *
        (star (Polynomial.eval c p) • (1 : E →L[ℂ] E))‖ ≤
        ‖Polynomial.aeval A p‖ *
          ‖star (Polynomial.eval c p) • (1 : E →L[ℂ] E)‖ :=
      norm_mul_le _ _
    _ = ‖Polynomial.aeval A p‖ * a := by
      rw [norm_smul, norm_star, norm_one, mul_one]
    _ ≤ (2 * m + a) * a := mul_le_mul_of_nonneg_right hpA ha
    _ ≤ m ^ 2 := hfactor
