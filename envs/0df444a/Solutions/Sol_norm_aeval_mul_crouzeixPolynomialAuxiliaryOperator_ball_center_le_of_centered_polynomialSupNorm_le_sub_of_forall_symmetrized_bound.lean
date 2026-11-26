-- Prove2me | solution 1 for norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_centered_polynomialSupNorm_le_sub_of_forall_symmetrized_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:33:55.05249+00:00
-- url     : https://prove2.me/submissions/f7089f7d-82d3-43ce-a1ce-0c3e08a3f479

import Definitions.Def_Operator_Crouzeix_ConvexRunge
import Definitions.Def_Operator_Crouzeix_NormalProduct
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_NumericalRange_Convex
import Definitions.Def_Operator_NumericalRange_Nonempty
import Definitions.Def_Operator_Crouzeix_NormalProductSymmetrized
import Theorems.Thm_norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_centered_scalar_bound_of_forall_symmetrized_bound

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
    (p : Polynomial ℂ)
    (hcentered : polynomialSupNorm
        (p - Polynomial.C (Polynomial.eval c p)) K ≤
      polynomialSupNorm p K - ‖Polynomial.eval c p‖) :
    ‖Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R
            ((norm_nonneg (A - c • 1)).trans_lt hA)) p‖ ≤
      polynomialSupNorm p K ^ 2 := by
  let m : ℝ := polynomialSupNorm p K
  let a : ℝ := ‖Polynomial.eval c p‖
  let q : Polynomial ℂ := p - Polynomial.C (Polynomial.eval c p)
  let r : ℝ := polynomialSupNorm q K
  have ha : 0 ≤ a := norm_nonneg _
  apply
    norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_centered_scalar_bound_of_forall_symmetrized_bound
      A c hA hsymm p
  have hrma : r ≤ m - a := hcentered
  have hmul : 2 * r ≤ 2 * (m - a) :=
    mul_le_mul_of_nonneg_left hrma (by norm_num)
  have hsquare : 0 ≤ (m - a) ^ 2 := sq_nonneg _
  calc
    (2 * r + a) * a ≤ (2 * (m - a) + a) * a :=
      mul_le_mul_of_nonneg_right (add_le_add hmul (le_refl a)) ha
    _ = (2 * m - a) * a := by ring
    _ ≤ m ^ 2 := by nlinarith only [hsquare]
