-- Prove2me | solution 1 for norm_aeval_add_star_le_two_mul_polynomialSupNorm_of_representation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:38:41.248306+00:00
-- url     : https://prove2.me/submissions/7f9545b9-5ff3-409d-ab2e-f140c5652cde

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
import Theorems.Thm_norm_eval_circleMap_le_polynomialSupNorm_closedBall
import Theorems.Thm_intervalIntegrable_deriv_circleMap_smul_resolvent
import Theorems.Thm_intervalIntegrable_circleKernel_add_adjoint
import Theorems.Thm_intervalIntegrable_eval_smul_circleKernel_add_adjoint
import Theorems.Thm_intervalIntegral_resolvent_doubleLayer_eq_four_pi_smul_one_of_cauchy
import Theorems.Thm_isPositive_add_adjoint_smul_resolvent_circleMap
import Theorems.Thm_norm_add_star_le_two_mul_of_doubleLayer_representation
import Theorems.Thm_polynomialSupNorm_nonneg
import Theorems.Thm_sphere_subset_resolventSet_of_closure_numericalRange_subset_ball


set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution (A : E →L[ℂ] E)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R) (hW : closure (numericalRange A) ⊆ Metric.ball c R)
    (p : ℂ[X]) (G : E →L[ℂ] E)
    (hrep : aeval A p + star G = (2 * Real.pi)⁻¹ • ∫ t in (0 : ℝ)..(2 * Real.pi),
      p.eval (circleMap c R t) •
        ((-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t) +
          ContinuousLinearMap.adjoint
            ((-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t))))
    (hCauchy : (∫ t in (0 : ℝ)..(2 * Real.pi),
      deriv (circleMap c R) t • resolvent A (circleMap c R t)) =
        (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E)) :
    ‖aeval A p + star G‖ ≤ 2 * polynomialSupNorm p (Metric.closedBall c R) := by
  have hρ : Metric.sphere c R ⊆ resolventSet ℂ A :=
    sphere_subset_resolventSet_of_closure_numericalRange_subset_ball A hW
  have hW' : numericalRange A ⊆ Metric.closedBall c R :=
    subset_closure.trans (hW.trans Metric.ball_subset_closedBall)
  refine norm_add_star_le_two_mul_of_doubleLayer_representation (aeval A p) G hrep
    (intervalIntegrable_circleKernel_add_adjoint A hρ hR)
    (intervalIntegrable_eval_smul_circleKernel_add_adjoint A hρ hR p)
    (fun t _ => (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
      (isPositive_add_adjoint_smul_resolvent_circleMap A hW' t))
    (intervalIntegral_resolvent_doubleLayer_eq_four_pi_smul_one_of_cauchy A (circleMap c R)
      (intervalIntegrable_deriv_circleMap_smul_resolvent A hρ hR) hCauchy)
    (polynomialSupNorm_nonneg p _)
    (fun t _ => norm_eval_circleMap_le_polynomialSupNorm_closedBall p c hR t)
