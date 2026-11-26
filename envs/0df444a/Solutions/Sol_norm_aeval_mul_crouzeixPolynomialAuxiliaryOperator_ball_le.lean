-- Prove2me | solution 1 for norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:27:37.378032+00:00
-- url     : https://prove2.me/submissions/034596c1-181d-4057-b7b0-9eef67ed44b0

import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_CircleAuxiliary
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Definitions.Def_Operator_Crouzeix_CircleProduct
import Theorems.Thm_norm_aeval_mul_le_polynomialSupNorm_sq_of_auxiliary_eq_eval_zero_smul_one
import Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_ball_eq_eval_zero_smul_one


set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Pointwise
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) {R : ℝ} (hR : ‖A‖ < R) (p : Polynomial ℂ) :
    ‖Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A
        (SmoothJordanDomain.ball 0 R ((norm_nonneg A).trans_lt hR)) p‖ ≤
      polynomialSupNorm p (Metric.closedBall (0 : ℂ) R) ^ 2 :=
  norm_aeval_mul_le_polynomialSupNorm_sq_of_auxiliary_eq_eval_zero_smul_one
    A ((norm_nonneg A).trans_lt hR) hR.le p _
      (crouzeixPolynomialAuxiliaryOperator_ball_eq_eval_zero_smul_one A hR p)
