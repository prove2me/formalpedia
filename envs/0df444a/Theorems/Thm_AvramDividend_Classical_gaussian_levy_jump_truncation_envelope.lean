-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_levy_jump_truncation_envelope
-- name    : AvramDividend.Classical.gaussian_levy_jump_truncation_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T08:30:39.53889+00:00
-- url     : https://prove2.me/theorems/e940b753-c9cc-494a-9d63-b751597179b1
-- title:
--   Lévy-square envelope for canonical negative-jump exponent
-- statement:
--   For θ,z≥0, the canonical negative-jump Lévy–Khintchine compensation |exp(−θz)−1+θ z 1_{z≤1}| is at most (1+θ²)min(1,z²). Prove the small-jump branch by the established positivity/quadratic exponential compensator bounds, and the large-jump branch by 0<exp(−θz)≤1. This enables direct real integrability of the unshifted exponent under the Lévy truncated-square moment.
-- source:
--   Proved gaussian_compensated_jump_pos_linear and gaussian_compensated_jump_quadratic; Real.exp_le_exp and elementary real polynomial arithmetic.

import Mathlib

theorem AvramDividend.Classical.gaussian_levy_jump_truncation_envelope
    (θ z : ℝ) (hθ : 0 ≤ θ) (hz : 0 ≤ z) :
    |Real.exp (-θ * z) - 1 + θ * (if z ≤ 1 then z else 0)| ≤
      (1 + θ ^ 2) * min 1 (z ^ 2) := by sorry
