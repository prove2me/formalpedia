-- Prove2me | solution 1 for polynomial_eq_zero_of_polynomialSupNorm_closedBall_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:21:16.139084+00:00
-- url     : https://prove2.me/submissions/003d1d6a-2d79-4eeb-9526-6023f84e2a93

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.DiscreteSubset
import Definitions.Def_Operator_Crouzeix_PolynomialSupNormZero
import Theorems.Thm_polynomial_eq_zero_of_polynomialSupNorm_eq_zero
section
open Polynomial ContinuousLinearMap
universe u
private theorem infinite_closedBall_of_pos (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (Metric.closedBall c R).Infinite := by
  have hball : (Metric.ball c R).Infinite := by
    apply Set.Infinite.of_accPt
    exact Metric.isOpen_ball.preperfect c (Metric.mem_ball_self hR)
  exact hball.mono Metric.ball_subset_closedBall
section AuxiliaryBounds
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
end AuxiliaryBounds
end

set_option autoImplicit false
open Polynomial ContinuousLinearMap
universe u
theorem _root_.solution
    (p : ℂ[X]) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hzero : polynomialSupNorm p (Metric.closedBall c R) = 0) :
    p = 0 :=
  polynomial_eq_zero_of_polynomialSupNorm_eq_zero p (isCompact_closedBall c R)
    (infinite_closedBall_of_pos c hR) hzero
