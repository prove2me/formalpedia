-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_constant_drift_spatial_derivative
-- name    : AppliedSDE.SarkkaSolin.gaussian_constant_drift_spatial_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T11:27:00.193079+00:00
-- url     : https://prove2.me/theorems/3e0bbbba-8478-4ad8-bebc-52eb2223157c
-- title:
--   Spatial derivative of the constant-drift Gaussian transition density
-- statement:
--   For a positive time increment t-s and nonzero diffusion variance q, the spatial derivative of the one-dimensional Gaussian transition density with mean shift b*(t-s) equals minus the centred spatial displacement divided by q*(t-s), times the original density. This is the gradient formula used in both forward and backward Kolmogorov Gaussian drift PDE theorems.
-- source:
--   Sarkka and Solin (2019), Chapter 5 Fokker Planck equation; targets 42c16e46-7d9b-4591-a070-70f18572bb2e and 0fda7328-b552-40b9-83b5-e9d2e94d9332.

import Mathlib
open MeasureTheory
open scoped Topology

theorem AppliedSDE.SarkkaSolin.gaussian_constant_drift_spatial_derivative
    (b q y s t x : ℝ) (hq : 0 < q) (hst : s < t) :
    let p : ℝ -> ℝ := fun z =>
      Real.exp (-((z - y - b * (t - s)) ^ 2 / (2 * q * (t - s)))) /
        Real.sqrt (2 * Real.pi * q * (t - s))
    deriv p x = -((x - y - b * (t - s)) / (q * (t - s))) * p x := by
  sorry
