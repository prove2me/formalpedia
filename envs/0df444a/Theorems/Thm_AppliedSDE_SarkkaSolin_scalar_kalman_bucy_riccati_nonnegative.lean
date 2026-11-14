-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_scalar_kalman_bucy_riccati_nonnegative
-- name    : AppliedSDE.SarkkaSolin.scalar_kalman_bucy_riccati_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:49:48.139063+00:00
-- url     : https://prove2.me/theorems/cb690e06-8db2-4225-9103-b46f9a60c5a1
-- title:
--   Scalar Kalman–Bucy covariance remains nonnegative under its Riccati equation
-- statement:
--   A scalar specialisation of Särkkä and Solin (2019), Algorithm 10.9, equation (10.38). For a linear state drift coefficient F, observation coefficient H, nonnegative process noise variance Q and positive observation noise variance R, suppose a real-valued covariance trajectory is continuous, differentiable at nonnegative times, starts nonnegative and satisfies the scalar Kalman–Bucy Riccati equation P′=2FP+Q−(H²/R)P². Then its covariance is nonnegative at every nonnegative time. This is an analytic invariant of the continuous-time covariance equation; it does not assert the full stochastic conditional-distribution correctness of Kalman–Bucy filtering.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   P'=2FP+Q-\frac{H^2}{R}P^2,\quad P(0)\geq0\ \Longrightarrow\ P(t)\geq0
--   $$
-- source:
--   Original derived from Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Algorithm 10.9, equation (10.38), printed p. 208. https://doi.org/10.1017/9781108186735

import Mathlib
open Filter
open scoped Topology

theorem AppliedSDE.SarkkaSolin.scalar_kalman_bucy_riccati_nonnegative
    (F H Q R : ℝ) (hQ : 0 ≤ Q) (hR : 0 < R)
    (P : ℝ → ℝ) (hP0 : 0 ≤ P 0)
    (hcont : Continuous P)
    (hdiff : ∀ t : ℝ, 0 ≤ t → DifferentiableAt ℝ P t)
    (hode : ∀ t : ℝ, 0 ≤ t →
      deriv P t = 2 * F * P t + Q - (H ^ 2 / R) * (P t) ^ 2) :
    ∀ t : ℝ, 0 ≤ t → 0 ≤ P t := by
  sorry
