-- Prove2me | solution 1 for norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_closedBall_of_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:49:57.991233+00:00
-- url     : https://prove2.me/submissions/cb2a966e-c620-4a64-97f5-5981f661148c

import Definitions.Def_Operator_Crouzeix_CircleKernel
import Definitions.Def_Operator_Crouzeix_DoubleLayer
import Definitions.Def_Operator_Crouzeix_DoubleLayerIntegral
import Definitions.Def_Operator_Crouzeix_SymmetrizedBound
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_Crouzeix_SymmetrizedAuxiliary
import Definitions.Def_Operator_Crouzeix_CircleProduct
import Definitions.Def_Operator_Crouzeix_Palencia
import Definitions.Def_Operator_Crouzeix_CircleAuxiliary
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
import Theorems.Thm_norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_closedBall_of_aux_eq
import Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_ball_eq_eval_zero_smul_one


set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) {R : ℝ} (hR : ‖A‖ < R) (p : ℂ[X]) :
    ‖aeval A p‖ ≤ (1 + Real.sqrt 2) * polynomialSupNorm p (Metric.closedBall (0 : ℂ) R) :=
  norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_closedBall_of_aux_eq A hR p
    (crouzeixPolynomialAuxiliaryOperator_ball_eq_eval_zero_smul_one A hR p)
