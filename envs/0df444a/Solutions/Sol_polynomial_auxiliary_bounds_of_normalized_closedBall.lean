-- Prove2me | solution 1 for polynomial_auxiliary_bounds_of_normalized_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:21:32.490395+00:00
-- url     : https://prove2.me/submissions/61031c62-ea06-40c0-85b9-d498b16bcc27

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.DiscreteSubset
import Definitions.Def_Operator_Crouzeix_PolynomialSupNormZero
import Theorems.Thm_polynomial_auxiliary_bounds_of_normalized_of_isCompact_infinite
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
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
theorem _root_.solution
    (A : H →L[ℂ] H) (Omega : SmoothJordanDomain) (c : ℂ) {R : ℝ}
    (hR : 0 < R) (p : Polynomial ℂ)
    (hnormalized : ∀ q : Polynomial ℂ,
      polynomialSupNorm q (Metric.closedBall c R) = 1 →
        ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A Omega q)‖ ≤ 2 ∧
        ‖Polynomial.aeval A q *
          crouzeixPolynomialAuxiliaryOperator A Omega q‖ ≤ 1) :
    ‖Polynomial.aeval A p +
        star (crouzeixPolynomialAuxiliaryOperator A Omega p)‖ ≤
          2 * polynomialSupNorm p (Metric.closedBall c R) ∧
      ‖Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
          polynomialSupNorm p (Metric.closedBall c R) ^ 2 :=
  polynomial_auxiliary_bounds_of_normalized_of_isCompact_infinite A Omega
    (Metric.closedBall c R) (isCompact_closedBall c R)
      (infinite_closedBall_of_pos c hR) p hnormalized
