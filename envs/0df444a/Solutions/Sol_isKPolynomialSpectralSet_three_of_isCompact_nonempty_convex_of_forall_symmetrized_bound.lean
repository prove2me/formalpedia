-- Prove2me | solution 1 for isKPolynomialSpectralSet_three_of_isCompact_nonempty_convex_of_forall_symmetrized_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:32:57.304809+00:00
-- url     : https://prove2.me/submissions/126b5962-9771-4a87-b35b-51ac30360004

import Definitions.Def_Operator_Crouzeix_ConvexRunge
import Definitions.Def_Operator_Crouzeix_NormalProduct
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_NumericalRange_Convex
import Definitions.Def_Operator_NumericalRange_Nonempty
import Definitions.Def_Operator_Crouzeix_NormalProductSymmetrized
import Theorems.Thm_circle_center_mem_of_isCompact_nonempty_convex_of_forall_symmetrized_bound
import Theorems.Thm_spectrum_subset_of_isCompact_nonempty_convex_of_forall_symmetrized_bound
import Theorems.Thm_norm_aeval_le_two_mul_polynomialSupNorm_sub_C_add_norm_eval_sub_two_mul_of_forall_symmetrized_bound
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



set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Pointwise
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) {K : Set ℂ}
    (hcompact : IsCompact K) (hnonempty : K.Nonempty) (hconvex : Convex ℝ K)
    (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q K) :
    IsKPolynomialSpectralSet A 3 K := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    refine ⟨?_, ?_⟩
    · rw [spectrum.of_subsingleton]
      exact Set.empty_subset K
    · intro p
      have hzero : Polynomial.aeval A p = 0 := Subsingleton.elim _ _
      rw [hzero, norm_zero]
      exact mul_nonneg (by norm_num) (polynomialSupNorm_nonneg p K)
  let _ := hE
  refine ⟨
    spectrum_subset_of_isCompact_nonempty_convex_of_forall_symmetrized_bound
      A hcompact hnonempty hconvex c hA hsymm, ?_⟩
  have hc : c ∈ K :=
    circle_center_mem_of_isCompact_nonempty_convex_of_forall_symmetrized_bound
      A hcompact hnonempty hconvex c hA hsymm
  intro p
  let m : ℝ := polynomialSupNorm p K
  have hpA :=
    norm_aeval_le_two_mul_polynomialSupNorm_sub_C_add_norm_eval_sub_two_mul_of_forall_symmetrized_bound
      A c hA hsymm p 0
  have hpc : ‖Polynomial.eval c p‖ ≤ m :=
    norm_eval_le_polynomialSupNorm p
      (bddAbove_norm_eval_image_of_isCompact p hcompact) hc
  calc
    ‖Polynomial.aeval A p‖ ≤ 2 * m + ‖Polynomial.eval c p‖ := by
      simpa only [m, Polynomial.C_0, sub_zero, mul_zero] using hpA
    _ ≤ 2 * m + m := add_le_add (le_refl (2 * m)) hpc
    _ = 3 * polynomialSupNorm p K := by ring
