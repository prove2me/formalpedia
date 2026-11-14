-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_two_observation_posterior_variance
-- name    : AppliedSDE.SarkkaSolin.ar1_two_observation_posterior_variance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:15:44.335191+00:00
-- url     : https://prove2.me/theorems/2eb63cae-2d89-4942-a9cb-14c8c1f62ea7
-- title:
--   Two-observation stationary AR(1) GP posterior variance equals Kalman variance
-- statement:
--   For stationary scalar Gaussian AR(1) state variance V>0, correlation factor 0<a<1, and independent observation noise variance r>0, the batch GP posterior variance of the second state after two observations, calculated using the explicit inverse of [[V+r,aV],[aV,V+r]], equals the two-step sequential Kalman posterior variance. This is an exact finite-dimensional posterior covariance identity and supports the all-sample-size AR1 GP/Kalman capstone.
-- source:
--   Särkkä and Solin, Applied Stochastic Differential Equations (2019), Chapters 10 and 12.

import Mathlib

theorem AppliedSDE.SarkkaSolin.ar1_two_observation_posterior_variance
    (a V r : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hV : 0 < V) (hr : 0 < r) :
    let D : ℝ := (V + r) ^ 2 - (a * V) ^ 2
    let P0 : ℝ := V * r / (V + r)
    let pred : ℝ := a ^ 2 * P0 + V * (1 - a ^ 2)
    V - ((a * V) ^ 2 * (V + r) -
         2 * (a * V) * V * (a * V) + V ^ 2 * (V + r)) / D =
      pred * r / (pred + r) := by
  sorry
