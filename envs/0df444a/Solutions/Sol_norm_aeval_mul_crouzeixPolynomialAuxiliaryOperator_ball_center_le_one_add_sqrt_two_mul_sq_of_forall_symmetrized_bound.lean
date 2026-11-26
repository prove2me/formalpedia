-- Prove2me | solution 1 for norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_one_add_sqrt_two_mul_sq_of_forall_symmetrized_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:59:45.175857+00:00
-- url     : https://prove2.me/submissions/e193e29c-c815-4219-89a3-1c700474917d

import Definitions.Def_Operator_Crouzeix_ConvexRunge
import Definitions.Def_Operator_Crouzeix_NormalProduct
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_NumericalRange_Convex
import Definitions.Def_Operator_NumericalRange_Nonempty
import Definitions.Def_Operator_Crouzeix_NormalProductSymmetrized
import Theorems.Thm_circle_center_mem_closure_numericalRange_of_forall_symmetrized_bound
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
import Theorems.Thm_crouzeix_palencia
import Theorems.Thm_isBounded_numericalRange
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_norm_eval_le_polynomialSupNorm
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
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q (closure (numericalRange A)))
    (p : Polynomial ℂ) :
    ‖Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R
            ((norm_nonneg (A - c • 1)).trans_lt hA)) p‖ ≤
      (1 + Real.sqrt 2) *
        polynomialSupNorm p (closure (numericalRange A)) ^ 2 := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    have hzero : Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R
            ((norm_nonneg (A - c • 1)).trans_lt hA)) p = 0 :=
      Subsingleton.elim _ _
    rw [hzero, norm_zero]
    exact mul_nonneg (add_nonneg zero_le_one (Real.sqrt_nonneg 2)) (sq_nonneg _)
  let _ := hE
  let m : ℝ := polynomialSupNorm p (closure (numericalRange A))
  have hcompact : IsCompact (closure (numericalRange A)) :=
    (isBounded_numericalRange A).isCompact_closure
  have hc : c ∈ closure (numericalRange A) :=
    circle_center_mem_closure_numericalRange_of_forall_symmetrized_bound
      A c hA hsymm
  have hpA : ‖Polynomial.aeval A p‖ ≤ (1 + Real.sqrt 2) * m :=
    (crouzeix_palencia A).2 p
  have hpc : ‖Polynomial.eval c p‖ ≤ m :=
    norm_eval_le_polynomialSupNorm p
      (bddAbove_norm_eval_image_of_isCompact p hcompact) hc
  rw [crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
    A c hA p]
  calc
    ‖Polynomial.aeval A p *
        (star (Polynomial.eval c p) • (1 : E →L[ℂ] E))‖ ≤
        ‖Polynomial.aeval A p‖ *
          ‖star (Polynomial.eval c p) • (1 : E →L[ℂ] E)‖ :=
      norm_mul_le _ _
    _ = ‖Polynomial.aeval A p‖ * ‖Polynomial.eval c p‖ := by
      rw [norm_smul, norm_star, norm_one, mul_one]
    _ ≤ ((1 + Real.sqrt 2) * m) * m :=
      mul_le_mul hpA hpc (norm_nonneg _)
        ((norm_nonneg _).trans hpA)
    _ = (1 + Real.sqrt 2) *
        polynomialSupNorm p (closure (numericalRange A)) ^ 2 := by
      simp only [m, pow_two]
      ring
