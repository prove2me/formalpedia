-- Prove2me | solution 1 for crouzeixPolynomialAuxiliaryOperator_ball_center_of_resolvent_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:31:32.98613+00:00
-- url     : https://prove2.me/submissions/01d2a6e8-1470-4e1e-93b0-ef639445e56f

import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_Crouzeix_CircleAuxiliary
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_AffineAuxiliary
import Theorems.Thm_Polynomial_eval_affineComposition
attribute [local simp] Polynomial.eval_affineComposition



set_option autoImplicit false
open Complex MeasureTheory
open scoped InnerProductSpace Interval Real
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ)
    (hshift : ∀ z : ℂ, resolvent (A - c • (1 : E →L[ℂ] E)) z =
      resolvent A (z + c)) :
    crouzeixPolynomialAuxiliaryOperator A (SmoothJordanDomain.ball c R hR) p =
      crouzeixPolynomialAuxiliaryOperator
        (A - c • (1 : E →L[ℂ] E)) (SmoothJordanDomain.ball 0 R hR)
          (p.affineComposition 1 c) := by
  unfold crouzeixPolynomialAuxiliaryOperator crouzeixAuxiliaryOperator
  congr 1
  unfold contourIntegral
  apply intervalIntegral.integral_congr
  intro t _
  change deriv (circleMap c R) t •
      (star (Polynomial.eval (circleMap c R t) p) •
        resolvent A (circleMap c R t)) =
    deriv (circleMap 0 R) t •
      (star (Polynomial.eval (circleMap 0 R t) (p.affineComposition 1 c)) •
        resolvent (A - c • (1 : E →L[ℂ] E)) (circleMap 0 R t))
  have hmap : circleMap c R t = circleMap 0 R t + c := by
    rw [← circleMap_sub_center c R t]
    ring
  have hderiv : deriv (circleMap c R) t = deriv (circleMap 0 R) t := by
    rw [deriv_circleMap, deriv_circleMap]
  rw [hderiv, hmap, hshift, Polynomial.eval_affineComposition, one_mul]
