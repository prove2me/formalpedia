-- Prove2me | solution 1 for spectrum_aeval_sub_eval_smul_one_subset_closedBall_of_forall_symmetrized_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:59:34.435997+00:00
-- url     : https://prove2.me/submissions/62643a23-0691-4337-b74f-db5af7b15b65

import Definitions.Def_Operator_Crouzeix_ConvexRunge
import Definitions.Def_Operator_Crouzeix_NormalProduct
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_NumericalRange_Convex
import Definitions.Def_Operator_NumericalRange_Nonempty
import Definitions.Def_Operator_Crouzeix_NormalProductSymmetrized
import Theorems.Thm_norm_pow_aeval_sub_eval_smul_one_le_two_mul_pow_polynomialSupNorm_sub_C_of_forall_symmetrized_bound
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
    {K : Set ℂ} (hK : IsCompact K)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q K)
    (p : Polynomial ℂ) :
    spectrum ℂ (Polynomial.aeval A p -
        Polynomial.eval c p • (1 : E →L[ℂ] E)) ⊆
      Metric.closedBall 0
        (polynomialSupNorm (p - Polynomial.C (Polynomial.eval c p)) K) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    rw [spectrum.of_subsingleton]
    exact Set.empty_subset _
  let _ := hE
  let T : E →L[ℂ] E := Polynomial.aeval A p -
    Polynomial.eval c p • (1 : E →L[ℂ] E)
  let m : ℝ := polynomialSupNorm
    (p - Polynomial.C (Polynomial.eval c p)) K
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hzm
  have hm : 0 ≤ m := polynomialSupNorm_nonneg _ _
  have hmz : m < ‖z‖ := lt_of_not_ge hzm
  have hzpos : 0 < ‖z‖ := hm.trans_lt hmz
  have hratio_nonneg : 0 ≤ m / ‖z‖ := div_nonneg hm hzpos.le
  have hratio_lt_one : m / ‖z‖ < 1 := (div_lt_one hzpos).2 hmz
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (m / ‖z‖) ^ n < (1 / 2 : ℝ) :=
    exists_pow_lt_of_lt_one (by norm_num) hratio_lt_one
  have hratio_succ : 2 * (m / ‖z‖) ^ (n + 1) < 1 := by
    have hratio_le_one : m / ‖z‖ ≤ 1 := hratio_lt_one.le
    have hpow_succ : (m / ‖z‖) ^ (n + 1) ≤ (m / ‖z‖) ^ n := by
      rw [pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg hratio_nonneg n) hratio_le_one
    nlinarith only [hn, hpow_succ]
  have hzpow_mem : z ^ (n + 1) ∈ spectrum ℂ (T ^ (n + 1)) :=
    spectrum.pow_mem_pow T (n + 1) hz
  have hzpow_le : ‖z‖ ^ (n + 1) ≤ ‖T ^ (n + 1)‖ := by
    simpa only [norm_pow] using spectrum.norm_le_norm_of_mem hzpow_mem
  have hTpow : ‖T ^ (n + 1)‖ ≤ 2 * m ^ (n + 1) := by
    simpa only [T, m] using
      norm_pow_aeval_sub_eval_smul_one_le_two_mul_pow_polynomialSupNorm_sub_C_of_forall_symmetrized_bound
        A c hA hK hsymm p n
  have hstrict : 2 * m ^ (n + 1) < ‖z‖ ^ (n + 1) := by
    calc
      2 * m ^ (n + 1) =
          (2 * (m / ‖z‖) ^ (n + 1)) * ‖z‖ ^ (n + 1) := by
            rw [div_pow]
            field_simp
      _ < 1 * ‖z‖ ^ (n + 1) :=
        mul_lt_mul_of_pos_right hratio_succ (pow_pos hzpos (n + 1))
      _ = ‖z‖ ^ (n + 1) := one_mul _
  exact (not_lt_of_ge (hzpow_le.trans hTpow)) hstrict
