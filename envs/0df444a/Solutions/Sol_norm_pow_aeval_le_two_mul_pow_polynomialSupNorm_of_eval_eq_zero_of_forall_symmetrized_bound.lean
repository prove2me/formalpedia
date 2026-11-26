-- Prove2me | solution 1 for norm_pow_aeval_le_two_mul_pow_polynomialSupNorm_of_eval_eq_zero_of_forall_symmetrized_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:32:02.460868+00:00
-- url     : https://prove2.me/submissions/5d17b648-2e82-4117-adb8-ddeb1f05deef

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
import Theorems.Thm_bddAbove_norm_eval_image_of_isCompact
import Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_norm_eval_le_polynomialSupNorm
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


section
open Complex Polynomial Set
open scoped InnerProductSpace Pointwise
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
private theorem polynomialSupNorm_pow_le_of_isCompact
    (p : Polynomial ℂ) {K : Set ℂ} (hK : IsCompact K) (n : ℕ) :
    polynomialSupNorm (p ^ n) K ≤ polynomialSupNorm p K ^ n := by
  unfold polynomialSupNorm
  refine Real.iSup_le (fun z ↦ ?_)
    (pow_nonneg (polynomialSupNorm_nonneg p K) n)
  refine Real.iSup_le (fun hz ↦ ?_)
    (pow_nonneg (polynomialSupNorm_nonneg p K) n)
  simp only [Polynomial.eval_pow, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (norm_eval_le_polynomialSupNorm p
      (bddAbove_norm_eval_image_of_isCompact p hK) hz) n
end

set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Pointwise
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    {K : Set ℂ} (hK : IsCompact K)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q K)
    (p : Polynomial ℂ) (hpc : Polynomial.eval c p = 0) (n : ℕ) :
    ‖Polynomial.aeval A p ^ (n + 1)‖ ≤
      2 * polynomialSupNorm p K ^ (n + 1) := by
  have hpow := hsymm (p ^ (n + 1))
  rw [crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
    A c hA (p ^ (n + 1))] at hpow
  simp only [map_pow, Polynomial.eval_pow, hpc,
    zero_pow (Nat.succ_ne_zero n), star_zero, zero_smul, add_zero] at hpow
  exact hpow.trans (mul_le_mul_of_nonneg_left
    (polynomialSupNorm_pow_le_of_isCompact p hK (n + 1)) (by positivity))
