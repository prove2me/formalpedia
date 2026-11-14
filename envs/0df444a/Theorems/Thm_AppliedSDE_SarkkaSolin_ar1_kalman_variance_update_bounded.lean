-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_kalman_variance_update_bounded
-- name    : AppliedSDE.SarkkaSolin.ar1_kalman_variance_update_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:03:47.529202+00:00
-- url     : https://prove2.me/theorems/2aa015b4-fba9-4de2-a299-647e957e099a
-- title:
--   AR(1) scalar Kalman variance update remains positive and below stationary variance
-- statement:
--   For 0<a<1, V>0 and independent observation noise r>0, if the current scalar Kalman posterior variance P satisfies 0≤P≤V, then the predicted variance a²P+V(1−a²) is strictly positive and its observation-updated variance predicted*r/(predicted+r) is strictly positive and at most V. This supplies the invariant interval needed in the finite-step induction for the AR(1) batch GP posterior versus sequential Kalman theorem 1b230031-7f34-4971-8d05-2f91cf171bd9. No claim about convergence of the numerical filter is included.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Chapter 10 scalar Kalman filter and Chapter 12 stationary OU state-space representation. https://doi.org/10.1017/9781108186735

import Mathlib

theorem AppliedSDE.SarkkaSolin.ar1_kalman_variance_update_bounded
    (a V r P : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1) (hV : 0 < V) (hr : 0 < r)
    (hP0 : 0 ≤ P) (hPV : P ≤ V) :
    let predicted : ℝ := a ^ 2 * P + V * (1 - a ^ 2)
    0 < predicted ∧
      0 < predicted * r / (predicted + r) ∧
      predicted * r / (predicted + r) ≤ V := by
  sorry
