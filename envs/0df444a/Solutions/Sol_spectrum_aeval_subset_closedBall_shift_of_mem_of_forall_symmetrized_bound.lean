-- Prove2me | solution 1 for spectrum_aeval_subset_closedBall_shift_of_mem_of_forall_symmetrized_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:49:08.490444+00:00
-- url     : https://prove2.me/submissions/ed22f589-04f8-42d0-9b60-87d947fe0c54

import Definitions.Def_Operator_Crouzeix_ConvexRunge
import Definitions.Def_Operator_Crouzeix_NormalProduct
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_NumericalRange_Convex
import Definitions.Def_Operator_NumericalRange_Nonempty
import Definitions.Def_Operator_Crouzeix_NormalProductSymmetrized
import Theorems.Thm_norm_shifted_aeval_pow_add_shifted_eval_pow_smul_one_le_two_mul_pow_polynomialSupNorm_of_forall_symmetrized_bound
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
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    {K : Set ℂ} (hK : IsCompact K) (hc : c ∈ K)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q K)
    (p : Polynomial ℂ) (b : ℂ) :
    spectrum ℂ (Polynomial.aeval A p) ⊆
      Metric.closedBall b (polynomialSupNorm (p - Polynomial.C b) K) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    rw [spectrum.of_subsingleton]
    exact Set.empty_subset _
  let _ := hE
  let T : E →L[ℂ] E := Polynomial.aeval A p -
    b • (1 : E →L[ℂ] E)
  let a : ℂ := Polynomial.eval c p - b
  let m : ℝ := polynomialSupNorm (p - Polynomial.C b) K
  have ha : ‖a‖ ≤ m := by
    have h := norm_eval_le_polynomialSupNorm (p - Polynomial.C b)
      (bddAbove_norm_eval_image_of_isCompact (p - Polynomial.C b) hK) hc
    simpa only [a, m, Polynomial.eval_sub, Polynomial.eval_C] using h
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm]
  let w : ℂ := z - b
  have hw : w ∈ spectrum ℂ T := by
    have hshift : spectrum ℂ T =
        spectrum ℂ (Polynomial.aeval A p) - ({b} : Set ℂ) := by
      dsimp only [T]
      rw [← Algebra.algebraMap_eq_smul_one,
        ← spectrum.sub_singleton_eq]
    rw [hshift]
    exact ⟨z, hz, b, Set.mem_singleton b, rfl⟩
  by_contra hwm
  have hm : 0 ≤ m := polynomialSupNorm_nonneg _ _
  have hmw : m < ‖w‖ := lt_of_not_ge hwm
  have hwpos : 0 < ‖w‖ := hm.trans_lt hmw
  have hratio_nonneg : 0 ≤ m / ‖w‖ := div_nonneg hm hwpos.le
  have hratio_lt_one : m / ‖w‖ < 1 := (div_lt_one hwpos).2 hmw
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (m / ‖w‖) ^ n < (1 / 3 : ℝ) :=
    exists_pow_lt_of_lt_one (by norm_num) hratio_lt_one
  have hratio_succ : 3 * (m / ‖w‖) ^ (n + 1) < 1 := by
    have hratio_le_one : m / ‖w‖ ≤ 1 := hratio_lt_one.le
    have hpow_succ : (m / ‖w‖) ^ (n + 1) ≤ (m / ‖w‖) ^ n := by
      rw [pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg hratio_nonneg n) hratio_le_one
    nlinarith only [hn, hpow_succ]
  have hwpow_mem : w ^ (n + 1) ∈ spectrum ℂ (T ^ (n + 1)) :=
    spectrum.pow_mem_pow T (n + 1) hw
  have hadd_mem : w ^ (n + 1) + a ^ (n + 1) ∈
      spectrum ℂ (T ^ (n + 1) +
        a ^ (n + 1) • (1 : E →L[ℂ] E)) := by
    rw [← Algebra.algebraMap_eq_smul_one, ← spectrum.add_singleton_eq]
    exact ⟨w ^ (n + 1), hwpow_mem, a ^ (n + 1),
      Set.mem_singleton _, rfl⟩
  have hadd_le : ‖w ^ (n + 1) + a ^ (n + 1)‖ ≤
      ‖T ^ (n + 1) + a ^ (n + 1) • (1 : E →L[ℂ] E)‖ :=
    spectrum.norm_le_norm_of_mem hadd_mem
  have hmoment : ‖T ^ (n + 1) +
      a ^ (n + 1) • (1 : E →L[ℂ] E)‖ ≤ 2 * m ^ (n + 1) := by
    simpa only [T, a, m] using
      norm_shifted_aeval_pow_add_shifted_eval_pow_smul_one_le_two_mul_pow_polynomialSupNorm_of_forall_symmetrized_bound
        A c hA hK hsymm p b n
  have hapow : ‖a‖ ^ (n + 1) ≤ m ^ (n + 1) :=
    pow_le_pow_left₀ (norm_nonneg _) ha (n + 1)
  have hwpow_le : ‖w‖ ^ (n + 1) ≤ 3 * m ^ (n + 1) := by
    calc
      ‖w‖ ^ (n + 1) = ‖w ^ (n + 1)‖ := (norm_pow w (n + 1)).symm
      _ = ‖(w ^ (n + 1) + a ^ (n + 1)) - a ^ (n + 1)‖ := by
        rw [add_sub_cancel_right]
      _ ≤ ‖w ^ (n + 1) + a ^ (n + 1)‖ + ‖a ^ (n + 1)‖ :=
        norm_sub_le _ _
      _ ≤ 2 * m ^ (n + 1) + m ^ (n + 1) := by
        simpa only [norm_pow] using add_le_add (hadd_le.trans hmoment) hapow
      _ = 3 * m ^ (n + 1) := by ring
  have hstrict : 3 * m ^ (n + 1) < ‖w‖ ^ (n + 1) := by
    calc
      3 * m ^ (n + 1) =
          (3 * (m / ‖w‖) ^ (n + 1)) * ‖w‖ ^ (n + 1) := by
            rw [div_pow]
            field_simp
      _ < 1 * ‖w‖ ^ (n + 1) :=
        mul_lt_mul_of_pos_right hratio_succ (pow_pos hwpos (n + 1))
      _ = ‖w‖ ^ (n + 1) := one_mul _
  exact (not_lt_of_ge hwpow_le) hstrict
