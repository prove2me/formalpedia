-- Prove2me | solution 1 for norm_aeval_le_polynomialSupNorm_closedBall_of_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:32:26.639774+00:00
-- url     : https://prove2.me/submissions/9ba7c199-6fd3-480a-86d4-1dfcb4c8f6bd

import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_CircleAuxiliary
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Definitions.Def_Operator_Crouzeix_CircleProduct
import Theorems.Thm_Polynomial_aeval_affineComposition
import Theorems.Thm_Polynomial_eval_affineComposition
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_polynomialSupNorm_affineComposition_image
import Theorems.Thm_vonNeumann_inequality
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
    (p : Polynomial ℂ) :
    ‖Polynomial.aeval A p‖ ≤
      polynomialSupNorm p (Metric.closedBall (0 : ℂ) R) := by
  let T : E →L[ℂ] E := (R : ℂ)⁻¹ • A
  let q := p.affineComposition (R : ℂ) 0
  have hT : ‖T‖ ≤ 1 := by
    dsimp only [T]
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    exact (inv_mul_le_one₀ hR).mpr hA
  have hEval : Polynomial.aeval T q = Polynomial.aeval A p := by
    dsimp only [q]
    rw [Polynomial.aeval_affineComposition]
    dsimp only [T]
    simp only [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hR.ne'), one_smul,
      zero_smul, add_zero]
  have hImage : ((fun z : ℂ => (R : ℂ) * z + 0) ''
      Metric.closedBall (0 : ℂ) 1) = Metric.closedBall (0 : ℂ) R := by
    simp only [add_zero, ← smul_eq_mul, Set.image_smul, smul_unitClosedBall,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  calc
    ‖Polynomial.aeval A p‖ = ‖Polynomial.aeval T q‖ := congrArg norm hEval.symm
    _ ≤ polynomialSupNorm q (Metric.closedBall (0 : ℂ) 1) :=
      vonNeumann_inequality T hT q
    _ = polynomialSupNorm p (Metric.closedBall (0 : ℂ) R) := by
      dsimp only [q]
      rw [polynomialSupNorm_affineComposition_image, hImage]
