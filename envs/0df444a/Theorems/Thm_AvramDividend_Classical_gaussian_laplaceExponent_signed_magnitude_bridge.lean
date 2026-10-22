-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_laplaceExponent_signed_magnitude_bridge
-- name    : AvramDividend.Classical.gaussian_laplaceExponent_signed_magnitude_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T12:10:25.435868+00:00
-- url     : https://prove2.me/theorems/6e075082-cb63-4309-b6b6-4a6d0efd0b44
-- title:
--   Canonical signed-jump Laplace exponent expressed in positive magnitudes
-- statement:
--   The actual mission's Lévy–Khintchine exponent laplaceExponent c σ ν θ, integrating negative jumps y<0 with an open-interval truncation, equals its Gaussian polynomial part plus a compensated exponential integral expressed in terms of positive jump magnitude z=-y with strict truncation z<1. This uses the independently published pointwise sign mirror and integral congruence on the negative half-line, preserving the measure ν and its boundary-atom convention. It is a noncircular model-level bridge towards the already proved positive-magnitude Gaussian Volterra exponent identity.
-- source:
--   Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy and gaussian_negative_jump_integrand_mirror.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set

theorem AvramDividend.Classical.gaussian_laplaceExponent_signed_magnitude_bridge (c σ : ℝ) (ν : Measure ℝ) (θ : ℝ) :
    laplaceExponent c σ ν θ =
      c * θ + σ ^ 2 * θ ^ 2 / 2 +
        (∫ y in Iio (0 : ℝ),
          Real.exp (-θ * (-y)) - 1 +
            θ * (if -y < 1 then -y else 0) ∂ν) := by sorry
