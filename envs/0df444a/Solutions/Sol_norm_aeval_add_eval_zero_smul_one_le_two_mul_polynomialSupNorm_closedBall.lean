-- Prove2me | solution 1 for norm_aeval_add_eval_zero_smul_one_le_two_mul_polynomialSupNorm_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:28:07.383355+00:00
-- url     : https://prove2.me/submissions/51d90d1c-d763-426e-8c89-1d9776b5e647

import Definitions.Def_Operator_Crouzeix_SpectralCauchy
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliary
import Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_ball_eq_eval_zero_smul_one_of_spectrum_subset_ball
import Theorems.Thm_Polynomial_aeval_affineComposition
import Theorems.Thm_Polynomial_eval_affineComposition
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_ball_le_of_closure_numericalRange_subset_ball
import Theorems.Thm_spectrum_subset_closure_numericalRange
attribute [local simp] Polynomial.aeval_affineComposition
attribute [local simp] Polynomial.eval_affineComposition
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex ComplexConjugate Polynomial Set spectrum
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) {r : ℝ} (hr : 0 < r)
    (hW : closure (numericalRange A) ⊆ Metric.ball (0 : ℂ) r) (p : Polynomial ℂ) :
    ‖Polynomial.aeval A p + Polynomial.eval 0 p • (1 : E →L[ℂ] E)‖ ≤
      2 * polynomialSupNorm p (Metric.closedBall (0 : ℂ) r) := by
  have hσ : spectrum ℂ A ⊆ Metric.ball (0 : ℂ) r :=
    (spectrum_subset_closure_numericalRange A).trans hW
  have hbound :=
    norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_ball_le_of_closure_numericalRange_subset_ball
      A hr hW p
  rw [crouzeixPolynomialAuxiliaryOperator_ball_eq_eval_zero_smul_one_of_spectrum_subset_ball
    A hr hσ p] at hbound
  simpa only [star_smul, star_star, star_one] using hbound
