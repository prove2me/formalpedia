-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_constant_drift_spatial_second_derivative
-- name    : AppliedSDE.SarkkaSolin.gaussian_constant_drift_spatial_second_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T11:28:21.526049+00:00
-- url     : https://prove2.me/theorems/ea77324b-e218-4dd2-95ae-87baeea7bdb8
-- title:
--   Second spatial derivative of the constant-drift Gaussian kernel
-- statement:
--   The second derivative of the Gaussian transition density equals density multiplied by the squared displacement divided by the squared variance minus inverse variance. A reusable spatial Laplacian identity for the Fokker-Planck and backward Kolmogorov equations.
-- source:
--   Sarkka and Solin (2019), Gaussian transition-density solution of Kolmogorov PDEs; complements first derivative theorem 3e0bbbba-8478-4ad8-bebc-52eb2223157c.

import Mathlib
open MeasureTheory
open scoped Topology

theorem AppliedSDE.SarkkaSolin.gaussian_constant_drift_spatial_second_derivative
    (b q y s t x : ℝ) (hq : 0 < q) (hst : s < t) :
    let p : ℝ -> ℝ := fun z =>
      Real.exp (-((z - y - b * (t - s)) ^ 2 / (2 * q * (t - s)))) /
        Real.sqrt (2 * Real.pi * q * (t - s))
    deriv (deriv p) x =
      (((x - y - b * (t - s)) ^ 2 / (q ^ 2 * (t - s) ^ 2)) -
        1 / (q * (t - s))) * p x := by
  sorry
