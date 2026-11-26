-- Prove2me | solution 1 for norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_ball_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:40:46.634276+00:00
-- url     : https://prove2.me/submissions/f36afb5c-3a4c-4dd1-b7a1-db0748716812

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
import Theorems.Thm_closure_numericalRange_subset_ball_of_norm_lt
import Theorems.Thm_norm_aeval_add_star_le_two_mul_polynomialSupNorm_of_representation_of_norm_lt
import Theorems.Thm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_eq_doubleLayerIntegral_of_cauchy
import Theorems.Thm_normalized_circleIntegral_eval_smul_resolvent_eq_aeval


set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution (A : E →L[ℂ] E) {R : ℝ}
    (hR : ‖A‖ < R) (p : ℂ[X]) :
    ‖aeval A p + star (crouzeixPolynomialAuxiliaryOperator A
        (SmoothJordanDomain.ball 0 R ((norm_nonneg A).trans_lt hR)) p)‖ ≤
      2 * polynomialSupNorm p (Metric.closedBall (0 : ℂ) R) := by
  have hRpos : 0 < R := (norm_nonneg A).trans_lt hR
  have hOmega : closure (numericalRange A) ⊆ (SmoothJordanDomain.ball 0 R hRpos).carrier :=
    closure_numericalRange_subset_ball_of_norm_lt A hR
  have hCauchy : aeval A p = (2 * (Real.pi : ℂ) * I)⁻¹ •
      contourIntegral (fun z => Polynomial.eval z p • resolvent A z)
        (SmoothJordanDomain.ball 0 R hRpos).boundaryParam :=
    (normalized_circleIntegral_eval_smul_resolvent_eq_aeval A hR p).symm
  have hrep := aeval_add_star_crouzeixPolynomialAuxiliaryOperator_eq_doubleLayerIntegral_of_cauchy
    A (SmoothJordanDomain.ball 0 R hRpos) p hOmega hCauchy
  exact norm_aeval_add_star_le_two_mul_polynomialSupNorm_of_representation_of_norm_lt A hR p _ hrep
