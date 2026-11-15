-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_constant_drift_time_derivative
-- name    : AppliedSDE.SarkkaSolin.gaussian_constant_drift_time_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T11:29:57.12221+00:00
-- url     : https://prove2.me/theorems/883545fd-f27a-4166-9294-e6d630db09bc
-- title:
--   Time derivative of the constant-drift Gaussian transition density
-- statement:
--   For t>s and q>0, the terminal-time derivative of the constant-drift Gaussian transition density equals itself times b times its centred displacement divided by variance, plus its squared displacement divided by twice its variance rate, minus reciprocal twice elapsed time. Together with first and second spatial derivatives, this proves the Gaussian Fokker-Planck equation.
-- source:
--   Sarkka and Solin (2019), Gaussian transition kernel Fokker-Planck solution theorem 42c16e46-7d9b-4591-a070-70f18572bb2e.

import Mathlib
open MeasureTheory
open scoped Topology

theorem AppliedSDE.SarkkaSolin.gaussian_constant_drift_time_derivative
    (b q y s t x : ℝ) (hq : 0 < q) (hst : s < t) :
    let p : ℝ -> ℝ := fun tau =>
      Real.exp (-((x - y - b * (tau - s)) ^ 2 / (2 * q * (tau - s)))) /
        Real.sqrt (2 * Real.pi * q * (tau - s))
    deriv p t =
      (b * (x - y - b * (t - s)) / (q * (t - s)) +
        (x - y - b * (t - s)) ^ 2 / (2 * q * (t - s) ^ 2) -
          1 / (2 * (t - s))) * p t := by
  sorry
