-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_two_observation_gp_kalman_mean
-- name    : AppliedSDE.SarkkaSolin.ar1_two_observation_gp_kalman_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:38:25.32626+00:00
-- url     : https://prove2.me/theorems/4b080200-aa80-4733-ab1b-241e4ca5103c
-- title:
--   Two-observation AR(1) Gaussian-process batch mean equals sequential Kalman mean
-- statement:
--   For a stationary scalar Gaussian AR(1) state observed twice with independent noise variance r, show that the explicit 2-by-2 covariance-inverse formula for the posterior mean of the second state agrees with the first two steps of the scalar Kalman filter. Parameters satisfy 0<a<1, V>0, r>0. This is the concrete two-observation case of the Open AppliedSDE.SarkkaSolin.ar1_batch_kalman_core, theorem 1b230031-7f34-4971-8d05-2f91cf171bd9.
-- source:
--   Särkkä and Solin, Applied Stochastic Differential Equations (2019), Chapters 10 and 12, Gaussian-process and Kalman-filter equivalence.

import Mathlib

theorem AppliedSDE.SarkkaSolin.ar1_two_observation_gp_kalman_mean
    (a V r y0 y1 : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hV : 0 < V) (hr : 0 < r) :
    let D : ℝ := (V + r) ^ 2 - (a * V) ^ 2
    let P0 : ℝ := V * r / (V + r)
    let pred : ℝ := a ^ 2 * P0 + V * (1 - a ^ 2)
    let m0 : ℝ := V / (V + r) * y0
    (a * V * ((V + r) * y0 - a * V * y1) +
      V * ((V + r) * y1 - a * V * y0)) / D =
        a * m0 + pred / (pred + r) * (y1 - a * m0) := by
  sorry
