-- Prove2me | solution 1 for norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_closedBall_of_norm_sub_smul_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:27:41.846264+00:00
-- url     : https://prove2.me/submissions/31a4fd61-298b-4a6e-a5c2-2381fdd0670b

import Definitions.Def_Operator_Crouzeix_AffineDisk
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
import Definitions.Def_Operator_Crouzeix_AffineCrouzeix
import Theorems.Thm_Polynomial_aeval_affineComposition
import Theorems.Thm_Polynomial_eval_affineComposition
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_closedBall_of_norm_lt
import Theorems.Thm_polynomialSupNorm_affineComposition_closedBall
attribute [local simp] Polynomial.aeval_affineComposition
attribute [local simp] Polynomial.eval_affineComposition
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open scoped InnerProductSpace Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R) (p : ℂ[X]) :
    ‖Polynomial.aeval A p‖ ≤
      (1 + Real.sqrt 2) * polynomialSupNorm p (Metric.closedBall c R) := by
  have hR : 0 < R := (norm_nonneg (A - c • (1 : E →L[ℂ] E))).trans_lt hA
  let T : E →L[ℂ] E := ((R : ℂ)⁻¹) • (A - c • 1)
  let q : ℂ[X] := p.affineComposition (R : ℂ) c
  have hT : ‖T‖ < 1 := by
    dsimp only [T]
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR.le]
    exact (inv_mul_lt_one₀ hR).mpr hA
  have hEval : Polynomial.aeval T q = Polynomial.aeval A p := by
    dsimp only [q]
    rw [Polynomial.aeval_affineComposition]
    congr 1
    dsimp only [T]
    rw [smul_smul]
    have hR0 : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
    rw [mul_inv_cancel₀ hR0, one_smul, sub_add_cancel]
  calc
    ‖Polynomial.aeval A p‖ = ‖Polynomial.aeval T q‖ := congrArg norm hEval.symm
    _ ≤ (1 + Real.sqrt 2) *
        polynomialSupNorm q (Metric.closedBall (0 : ℂ) 1) :=
      norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_closedBall_of_norm_lt T hT q
    _ = (1 + Real.sqrt 2) * polynomialSupNorm p (Metric.closedBall c R) := by
      rw [polynomialSupNorm_affineComposition_closedBall p c hR.le]
