-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_time_density_quotient_algebra
-- name    : AppliedSDE.SarkkaSolin.gaussian_time_density_quotient_algebra
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:26:07.296278+00:00
-- url     : https://prove2.me/theorems/f6fb5cec-5d65-4936-b75c-6ae9ac6648e8
-- title:
--   Scalar quotient-rule algebra for the Gaussian transition-density time derivative
-- statement:
--   The rational expression obtained by differentiating a Gaussian exponential divided by a square-root normaliser equals the Gaussian logarithmic time-derivative factor multiplied by its density. The identity uses nonzero q, elapsed time d and square-root scale S with S squared equal to 2 pi q d.
-- source:
--   Sarkka and Solin (2019), Gaussian Kolmogorov forward PDE time derivative; supporting theorem 883545fd-f27a-4166-9294-e6d630db09bc.

import Mathlib
open MeasureTheory

theorem AppliedSDE.SarkkaSolin.gaussian_time_density_quotient_algebra
    (b q d g S E : ℝ)
    (hq : q ≠ 0) (hd : d ≠ 0) (hS : S ≠ 0)
    (hSsq : S ^ 2 = 2 * Real.pi * q * d) :
    ((E * (-((2 * g * (-b) * (2 * q * d) - g ^ 2 * (2 * q)) /
        (2 * q * d) ^ 2))) * S -
      E * ((2 * Real.pi * q) / (2 * S))) / S ^ 2 =
    (b * g / (q * d) + g ^ 2 / (2 * q * d ^ 2) - 1 / (2 * d)) *
      E / S := by
  sorry
