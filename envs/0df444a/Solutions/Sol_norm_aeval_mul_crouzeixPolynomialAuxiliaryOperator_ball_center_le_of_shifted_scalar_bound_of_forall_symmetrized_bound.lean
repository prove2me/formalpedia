-- Prove2me | solution 1 for norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_shifted_scalar_bound_of_forall_symmetrized_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:51:06.90863+00:00
-- url     : https://prove2.me/submissions/348bd0e3-1e66-47e6-a647-3cd53a411953

import Definitions.Def_Operator_Crouzeix_ConvexRunge
import Definitions.Def_Operator_Crouzeix_NormalProduct
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_NumericalRange_Convex
import Definitions.Def_Operator_NumericalRange_Nonempty
import Definitions.Def_Operator_Crouzeix_NormalProductSymmetrized
import Theorems.Thm_norm_aeval_le_two_mul_polynomialSupNorm_sub_C_add_norm_eval_sub_two_mul_of_forall_symmetrized_bound
import Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one


set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Pointwise
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    {K : Set ℂ}
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q K)
    (p : Polynomial ℂ) (b : ℂ)
    (hscalar :
      (2 * polynomialSupNorm (p - Polynomial.C b) K +
        ‖Polynomial.eval c p - 2 * b‖) * ‖Polynomial.eval c p‖ ≤
      polynomialSupNorm p K ^ 2) :
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
  have ha : 0 ≤ a := norm_nonneg _
  have hpA : ‖Polynomial.aeval A p‖ ≤
      2 * polynomialSupNorm (p - Polynomial.C b) K +
        ‖Polynomial.eval c p - 2 * b‖ :=
    norm_aeval_le_two_mul_polynomialSupNorm_sub_C_add_norm_eval_sub_two_mul_of_forall_symmetrized_bound
      A c hA hsymm p b
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
    _ ≤ (2 * polynomialSupNorm (p - Polynomial.C b) K +
          ‖Polynomial.eval c p - 2 * b‖) * a :=
      mul_le_mul_of_nonneg_right hpA ha
    _ ≤ m ^ 2 := hscalar
