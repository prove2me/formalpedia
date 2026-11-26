-- Prove2me | solution 1 for norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:27:57.813067+00:00
-- url     : https://prove2.me/submissions/c976d62d-bf75-4bfc-a3d1-3f12e2b3d5cc

import Definitions.Def_Operator_Crouzeix_AffineAuxiliary
import Definitions.Def_Operator_Crouzeix_AffineDisk
import Definitions.Def_Operator_Crouzeix_AffineProduct
import Theorems.Thm_norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_le_of_auxiliary_eq_eval_center_smul_one
import Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one


set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R) (p : Polynomial ℂ) :
    ‖Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R ((norm_nonneg (A - c • 1)).trans_lt hA)) p‖ ≤
      polynomialSupNorm p (Metric.closedBall c R) ^ 2 :=
  norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_le_of_auxiliary_eq_eval_center_smul_one
    A c ((norm_nonneg (A - c • 1)).trans_lt hA) hA.le p
      (crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one A c hA p)
