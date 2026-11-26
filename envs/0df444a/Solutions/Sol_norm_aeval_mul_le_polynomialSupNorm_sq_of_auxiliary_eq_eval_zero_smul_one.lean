-- Prove2me | solution 1 for norm_aeval_mul_le_polynomialSupNorm_sq_of_auxiliary_eq_eval_zero_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:33:13.030502+00:00
-- url     : https://prove2.me/submissions/afb3339f-b563-4e4f-b181-d84b0b99bd35

import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_CircleAuxiliary
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Definitions.Def_Operator_Crouzeix_CircleProduct
import Theorems.Thm_norm_aeval_le_polynomialSupNorm_closedBall_of_norm_le
import Theorems.Thm_Polynomial_aeval_affineComposition
import Theorems.Thm_Polynomial_eval_affineComposition
import Theorems.Thm_bddAbove_norm_eval_image_of_isCompact
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_norm_eval_le_polynomialSupNorm
attribute [local simp] Polynomial.aeval_affineComposition
attribute [local simp] Polynomial.eval_affineComposition
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Pointwise
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) {R : ℝ} (hR : 0 < R) (hA : ‖A‖ ≤ R)
    (p : Polynomial ℂ) (G : E →L[ℂ] E)
    (hG : G = star (Polynomial.eval 0 p) • (1 : E →L[ℂ] E)) :
    ‖Polynomial.aeval A p * G‖ ≤
      polynomialSupNorm p (Metric.closedBall (0 : ℂ) R) ^ 2 := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    have hzero : Polynomial.aeval A p * G = 0 := Subsingleton.elim _ _
    rw [hzero, norm_zero]
    exact sq_nonneg _
  let _ := hE
  let m := polynomialSupNorm p (Metric.closedBall (0 : ℂ) R)
  have hpA : ‖Polynomial.aeval A p‖ ≤ m :=
    norm_aeval_le_polynomialSupNorm_closedBall_of_norm_le A hR hA p
  have hp0 : ‖Polynomial.eval 0 p‖ ≤ m :=
    norm_eval_le_polynomialSupNorm p
      (bddAbove_norm_eval_image_of_isCompact p (isCompact_closedBall (0 : ℂ) R))
      (Metric.mem_closedBall_self hR.le)
  rw [hG]
  calc
    ‖Polynomial.aeval A p *
        (star (Polynomial.eval 0 p) • (1 : E →L[ℂ] E))‖ ≤
        ‖Polynomial.aeval A p‖ *
          ‖star (Polynomial.eval 0 p) • (1 : E →L[ℂ] E)‖ := norm_mul_le _ _
    _ = ‖Polynomial.aeval A p‖ * ‖Polynomial.eval 0 p‖ := by
      rw [norm_smul, norm_star, norm_one, mul_one]
    _ ≤ m * m := mul_le_mul hpA hp0 (norm_nonneg _) ((norm_nonneg _).trans hpA)
    _ = polynomialSupNorm p (Metric.closedBall (0 : ℂ) R) ^ 2 := by
      simp only [m, pow_two]
