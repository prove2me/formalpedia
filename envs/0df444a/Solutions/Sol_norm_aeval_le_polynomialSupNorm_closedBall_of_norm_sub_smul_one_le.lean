-- Prove2me | solution 1 for norm_aeval_le_polynomialSupNorm_closedBall_of_norm_sub_smul_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:01:44.834497+00:00
-- url     : https://prove2.me/submissions/83a85db7-a6d3-4d26-af9a-ecd32b4aa0e9

import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_Crouzeix_AffineDisk
import Theorems.Thm_polynomialSupNorm_affineComposition_closedBall
import Theorems.Thm_Polynomial_aeval_affineComposition
import Theorems.Thm_Polynomial_eval_affineComposition
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_vonNeumann_inequality
attribute [local simp] Polynomial.aeval_affineComposition
attribute [local simp] Polynomial.eval_affineComposition
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open scoped InnerProductSpace Pointwise Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hA : ‖A - c • 1‖ ≤ R) (p : ℂ[X]) :
    ‖Polynomial.aeval A p‖ ≤ polynomialSupNorm p (Metric.closedBall c R) := by
  let T : E →L[ℂ] E := ((R : ℂ)⁻¹) • (A - c • 1)
  let q : ℂ[X] := p.affineComposition (R : ℂ) c
  have hT : ‖T‖ ≤ 1 := by
    dsimp only [T]
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR.le]
    exact (inv_mul_le_one₀ hR).mpr hA
  have hAeval : Polynomial.aeval T q = Polynomial.aeval A p := by
    dsimp only [q]
    rw [Polynomial.aeval_affineComposition]
    congr 1
    dsimp only [T]
    rw [smul_smul]
    have hR0 : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
    rw [mul_inv_cancel₀ hR0, one_smul, sub_add_cancel]
  calc
    ‖Polynomial.aeval A p‖ = ‖Polynomial.aeval T q‖ := congrArg norm hAeval.symm
    _ ≤ polynomialSupNorm q (Metric.closedBall (0 : ℂ) 1) :=
      vonNeumann_inequality T hT q
    _ = polynomialSupNorm p (Metric.closedBall c R) :=
      polynomialSupNorm_affineComposition_closedBall p c hR.le
