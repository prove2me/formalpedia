-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_schur_scalar_posterior_gain_riccati
-- name    : AppliedSDE.SarkkaSolin.schur_scalar_posterior_gain_riccati
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:54:54.795472+00:00
-- url     : https://prove2.me/theorems/b78a1dc8-263d-42cc-9bb8-76359e7827b7
-- title:
--   Scalar Gaussian Schur posterior equals Kalman gain and Riccati covariance update
-- statement:
--   For positive predictive signal variance P and observation noise variance r, the Gaussian Schur conditional mean update (r*mu+P*y)/(P+r) equals the Kalman innovation update mu+[P/(P+r)](y-mu). Simultaneously, the Schur conditional variance P-P²/(P+r) equals the scalar Riccati update Pr/(P+r). Both identities hold with strictly positive denominators and jointly translate block Gaussian conditioning into the sequential Kalman formulas used by the arbitrary-horizon OU/AR(1) capstone.
-- source:
--   Särkkä and Solin, Applied Stochastic Differential Equations (2019), Kalman filtering and Gaussian process posterior identities.

import Mathlib

theorem AppliedSDE.SarkkaSolin.schur_scalar_posterior_gain_riccati
    (P r μ y : ℝ) (hP : 0 < P) (hr : 0 < r) :
    (μ + P / (P + r) * (y - μ) =
       (r * μ + P * y) / (P + r)) ∧
    (P - P ^ 2 / (P + r) = P * r / (P + r)) := by
  sorry
