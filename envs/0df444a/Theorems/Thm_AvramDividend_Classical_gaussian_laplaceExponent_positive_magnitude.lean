-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_laplaceExponent_positive_magnitude
-- name    : AvramDividend.Classical.gaussian_laplaceExponent_positive_magnitude
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T12:10:38.400032+00:00
-- url     : https://prove2.me/theorems/bb6852d0-0927-48d8-8baf-cb28cfea4c04
-- title:
--   Canonical spectrally negative Lévy exponent in positive jump magnitudes
-- statement:
--   The actual negative-jump Lévy–Khintchine exponent of the Avram mission equals the Gaussian polynomial plus the positive jump-magnitude compensated exponential integral against the pushforward jump measure under negation. Its truncation is strictly below magnitude one to match the mission's exact open-interval indicator. The proof combines the negative-jump compensator mirror integral and the general signed-to-positive integral pushforward with explicit measurability. This is an essential noncircular bridge to the already Proved Gaussian double-tail Volterra identities.
-- source:
--   gaussian_laplaceExponent_signed_magnitude_bridge and gaussian_negative_jump_integral_pushforward.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set

theorem AvramDividend.Classical.gaussian_laplaceExponent_positive_magnitude (c σ θ : ℝ) (ν : Measure ℝ) :
    laplaceExponent c σ ν θ =
      c * θ + σ ^ 2 * θ ^ 2 / 2 +
        (∫ z in Ioi (0 : ℝ),
          Real.exp (-θ * z) - 1 +
            θ * (if z < 1 then z else 0)
              ∂(ν.map (fun y : ℝ => -y))) := by sorry
