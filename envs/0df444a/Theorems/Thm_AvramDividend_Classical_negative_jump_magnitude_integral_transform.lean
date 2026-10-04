-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_jump_magnitude_integral_transform
-- name    : AvramDividend.Classical.negative_jump_magnitude_integral_transform
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T08:14:35.400822+00:00
-- url     : https://prove2.me/theorems/e576610a-0af5-46e1-827c-d2007cf5f5c2
-- title:
--   Exact negative-jump exponential integral as a positive jump-magnitude pushforward integral
-- statement:
--   For every real jump measure and real theta, the real-valued integral of 1-exp(-theta*z) against the pushforward y↦max(-y,0) equals its negative-jump integral 1-exp(theta*y) over (-infinity,0). The positive and zero jumps map to z=0, where the integrand vanishes. This is the exact change-of-variables step for the bounded-variation Lévy–Khintchine rearrangement and avoids a premise that the original measure has no positive support. The real Lebesgue integrals use Mathlib's integral_map and integral_indicator.
-- source:
--   Pinned Mathlib integral_map and integral_indicator; canonical Classical Lévy negative jump conventions

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.negative_jump_magnitude_integral_transform (ν : Measure ℝ) (θ : ℝ) :
    (∫ z : ℝ≥0, (1 - Real.exp (-θ * (z : ℝ)))
      ∂(ν.map (fun y : ℝ => Real.toNNReal (-y)))) =
    ∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂ν := by
  sorry
