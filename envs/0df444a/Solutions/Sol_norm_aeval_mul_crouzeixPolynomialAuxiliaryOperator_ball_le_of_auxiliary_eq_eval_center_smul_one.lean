-- Prove2me | solution 1 for norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_le_of_auxiliary_eq_eval_center_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:39:33.998064+00:00
-- url     : https://prove2.me/submissions/775105ca-9419-4cdc-bb96-3bd847b41094

import Definitions.Def_Operator_Crouzeix_AffineAuxiliary
import Definitions.Def_Operator_Crouzeix_AffineDisk
import Definitions.Def_Operator_Crouzeix_AffineProduct
import Theorems.Thm_Polynomial_aeval_affineComposition
import Theorems.Thm_Polynomial_eval_affineComposition
import Theorems.Thm_bddAbove_norm_eval_image_of_isCompact
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_norm_aeval_le_polynomialSupNorm_closedBall_of_norm_sub_smul_one_le
import Theorems.Thm_norm_eval_le_polynomialSupNorm
attribute [local simp] Polynomial.aeval_affineComposition
attribute [local simp] Polynomial.eval_affineComposition
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ ≤ R) (p : Polynomial ℂ)
    (hG : crouzeixPolynomialAuxiliaryOperator A (SmoothJordanDomain.ball c R hR) p =
      star (Polynomial.eval c p) • (1 : E →L[ℂ] E)) :
    ‖Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A (SmoothJordanDomain.ball c R hR) p‖ ≤
      polynomialSupNorm p (Metric.closedBall c R) ^ 2 := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    have hzero : Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A (SmoothJordanDomain.ball c R hR) p = 0 :=
      Subsingleton.elim _ _
    rw [hzero, norm_zero]
    exact sq_nonneg _
  let _ := hE
  let m := polynomialSupNorm p (Metric.closedBall c R)
  have hpA : ‖Polynomial.aeval A p‖ ≤ m :=
    norm_aeval_le_polynomialSupNorm_closedBall_of_norm_sub_smul_one_le A c hR hA p
  have hpc : ‖Polynomial.eval c p‖ ≤ m :=
    norm_eval_le_polynomialSupNorm p
      (bddAbove_norm_eval_image_of_isCompact p (isCompact_closedBall c R))
      (Metric.mem_closedBall_self hR.le)
  rw [hG]
  calc
    ‖Polynomial.aeval A p *
        (star (Polynomial.eval c p) • (1 : E →L[ℂ] E))‖ ≤
        ‖Polynomial.aeval A p‖ *
          ‖star (Polynomial.eval c p) • (1 : E →L[ℂ] E)‖ := norm_mul_le _ _
    _ = ‖Polynomial.aeval A p‖ * ‖Polynomial.eval c p‖ := by
      rw [norm_smul, norm_star, norm_one, mul_one]
    _ ≤ m * m := mul_le_mul hpA hpc (norm_nonneg _) ((norm_nonneg _).trans hpA)
    _ = polynomialSupNorm p (Metric.closedBall c R) ^ 2 := by
      simp only [m, pow_two]
