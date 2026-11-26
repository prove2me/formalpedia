-- Prove2me | solution 1 for spectrum_subset_of_isCompact_nonempty_convex_of_forall_symmetrized_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:59:51.028548+00:00
-- url     : https://prove2.me/submissions/36db7d37-5405-4702-abba-5289cdd0afd0

import Definitions.Def_Operator_Crouzeix_ConvexRunge
import Definitions.Def_Operator_Crouzeix_NormalProduct
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_NumericalRange_Convex
import Definitions.Def_Operator_NumericalRange_Nonempty
import Definitions.Def_Operator_Crouzeix_NormalProductSymmetrized
import Theorems.Thm_spectrum_aeval_subset_closedBall_shift_of_isCompact_nonempty_convex_of_forall_symmetrized_bound
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
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_exists_polynomial_separator_of_isCompact_nonempty_convex
import Theorems.Thm_mem_numericalRange
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
    spectrum ℂ A ⊆ K := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    rw [spectrum.of_subsingleton]
    exact Set.empty_subset K
  let _ := hE
  intro z hz
  by_contra hzK
  obtain ⟨p, r, hr0, hr1, hpz, hpK⟩ :=
    exists_polynomial_separator_of_isCompact_nonempty_convex
      K hcompact hnonempty hconvex hzK
  have hsup : polynomialSupNorm p K ≤ r := by
    unfold polynomialSupNorm
    refine Real.iSup_le (fun w ↦ ?_) hr0
    exact Real.iSup_le (fun hw ↦ hpK w hw) hr0
  have hpzspec : Polynomial.eval z p ∈
      spectrum ℂ (Polynomial.aeval A p) := by
    rw [spectrum.map_polynomial_aeval]
    exact ⟨z, hz, rfl⟩
  have hpzball :=
    spectrum_aeval_subset_closedBall_shift_of_isCompact_nonempty_convex_of_forall_symmetrized_bound
      A hcompact hnonempty hconvex c hA hsymm p 0 hpzspec
  rw [Metric.mem_closedBall, dist_zero_right] at hpzball
  have hone : 1 ≤ polynomialSupNorm p K := by
    simpa only [hpz, norm_one, Polynomial.C_0, sub_zero] using hpzball
  exact (not_le_of_gt hr1) (hone.trans hsup)
