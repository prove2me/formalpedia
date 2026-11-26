-- Prove2me | solution 1 for norm_aeval_add_star_le_two_mul_polynomialSupNorm_of_representation_of_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:39:33.347584+00:00
-- url     : https://prove2.me/submissions/e12fc222-5f93-403f-9d83-8e2f64e40f87

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
import Theorems.Thm_norm_aeval_add_star_le_two_mul_polynomialSupNorm_of_representation
import Theorems.Thm_closure_numericalRange_subset_ball_of_norm_lt
import Theorems.Thm_intervalIntegral_deriv_circleMap_smul_resolvent_eq

set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) {R : ℝ} (hR : ‖A‖ < R) (p : ℂ[X]) (G : E →L[ℂ] E)
    (hrep : aeval A p + star G = (2 * Real.pi)⁻¹ • ∫ t in (0 : ℝ)..(2 * Real.pi),
      p.eval (circleMap 0 R t) •
        ((-I * deriv (circleMap 0 R) t) • resolvent A (circleMap 0 R t) +
          ContinuousLinearMap.adjoint
            ((-I * deriv (circleMap 0 R) t) • resolvent A (circleMap 0 R t)))) :
    ‖aeval A p + star G‖ ≤ 2 * polynomialSupNorm p (Metric.closedBall (0 : ℂ) R) :=
  norm_aeval_add_star_le_two_mul_polynomialSupNorm_of_representation A
    ((norm_nonneg A).trans hR.le) (closure_numericalRange_subset_ball_of_norm_lt A hR) p G hrep
    (intervalIntegral_deriv_circleMap_smul_resolvent_eq A hR)
