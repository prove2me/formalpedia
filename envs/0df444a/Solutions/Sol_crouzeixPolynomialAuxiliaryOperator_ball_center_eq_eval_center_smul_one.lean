-- Prove2me | solution 1 for crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:33:09.660058+00:00
-- url     : https://prove2.me/submissions/0967ddaf-42ae-4790-a8d3-0e9bc486581b

import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_Crouzeix_CircleAuxiliary
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_AffineAuxiliary
import Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_ball_center
import Theorems.Thm_Polynomial_aeval_affineComposition
import Theorems.Thm_Polynomial_eval_affineComposition
import Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_ball_eq_eval_zero_smul_one
import Theorems.Thm_mem_numericalRange
attribute [local simp] Polynomial.aeval_affineComposition
attribute [local simp] Polynomial.eval_affineComposition
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex MeasureTheory
open scoped InnerProductSpace Interval Real
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    (p : Polynomial ℂ) :
    crouzeixPolynomialAuxiliaryOperator A
        (SmoothJordanDomain.ball c R ((norm_nonneg (A - c • 1)).trans_lt hA)) p =
      star (Polynomial.eval c p) • (1 : E →L[ℂ] E) := by
  rw [crouzeixPolynomialAuxiliaryOperator_ball_center]
  rw [crouzeixPolynomialAuxiliaryOperator_ball_eq_eval_zero_smul_one
    (A - c • (1 : E →L[ℂ] E)) hA]
  simp only [Polynomial.eval_affineComposition, one_mul, zero_add]
