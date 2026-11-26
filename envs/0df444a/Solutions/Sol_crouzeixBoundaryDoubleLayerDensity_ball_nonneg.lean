-- Prove2me | solution 1 for crouzeixBoundaryDoubleLayerDensity_ball_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:05:04.668079+00:00
-- url     : https://prove2.me/submissions/289071a3-17f4-44a7-8070-540cb64ccf47

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureCircle
import Theorems.Thm_crouzeixBoundaryDoubleLayerDensity_ball_eq_inv_two_pi_of_ne

set_option autoImplicit false
open Complex MeasureTheory Set
open scoped ComplexConjugate Interval Real
theorem _root_.solution
    {c xi : ℂ} {R : ℝ} (hR : 0 < R)
    (hxi : xi ∈ Metric.sphere c R) (t : ℝ) :
    0 ≤ crouzeixBoundaryDoubleLayerDensity
      (SmoothJordanDomain.ball c R hR) xi t := by
  by_cases hne : circleMap c R t ≠ xi
  · rw [
      crouzeixBoundaryDoubleLayerDensity_ball_eq_inv_two_pi_of_ne
        hR hxi t hne]
    exact inv_nonneg.mpr (mul_nonneg (by norm_num) Real.pi_pos.le)
  · have heq : circleMap c R t = xi := not_ne_iff.mp hne
    unfold crouzeixBoundaryDoubleLayerDensity
    change 0 ≤ (deriv (circleMap c R) t *
      (circleMap c R t - xi)⁻¹).im / Real.pi
    rw [heq, sub_self, inv_zero, mul_zero, zero_im, zero_div]
