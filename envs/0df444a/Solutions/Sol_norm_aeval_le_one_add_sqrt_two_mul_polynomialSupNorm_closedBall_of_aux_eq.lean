-- Prove2me | solution 1 for norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_closedBall_of_aux_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:41:55.304795+00:00
-- url     : https://prove2.me/submissions/83b6d705-2357-42a4-9fae-d213bc1dcd1d

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
import Theorems.Thm_norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_ball_le
import Theorems.Thm_norm_aeval_mul_le_polynomialSupNorm_sq_of_auxiliary_eq_eval_zero_smul_one
import Theorems.Thm_norm_le_one_add_sqrt_two_mul_of_auxiliary_bounds


set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) {R : ℝ} (hR : ‖A‖ < R) (p : ℂ[X])
    (hG : crouzeixPolynomialAuxiliaryOperator A
        (SmoothJordanDomain.ball 0 R ((norm_nonneg A).trans_lt hR)) p =
      star (p.eval 0) • (1 : E →L[ℂ] E)) :
    ‖aeval A p‖ ≤ (1 + Real.sqrt 2) * polynomialSupNorm p (Metric.closedBall (0 : ℂ) R) :=
  norm_le_one_add_sqrt_two_mul_of_auxiliary_bounds (aeval A p) _
    (norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_ball_le A hR p)
    (norm_aeval_mul_le_polynomialSupNorm_sq_of_auxiliary_eq_eval_zero_smul_one A
      ((norm_nonneg A).trans_lt hR) hR.le p _ hG)
