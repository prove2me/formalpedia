-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_compensator_envelope
-- name    : AvramDividend.Classical.gaussian_esscher_compensator_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T06:34:49.983124+00:00
-- url     : https://prove2.me/theorems/a88fc591-cf29-4dc1-af8b-05915f79d26e
-- title:
--   Esscher-damped Gaussian jump compensator dominated by the Lévy quadratic-linear tail
-- statement:
--   For φ>0, θ≥0 and z≥0, the tilted jump-compensator exp(−φz)(exp(−θz)−1+θz) is at most (θ+θ²)exp(−φz)min(z²,z). For z≤1 the quadratic bound controls small jumps and for z≥1 the linear bound controls large jumps. This exact envelope has finite integral by the already-Proved Esscher-tilted Lévy-tail area integrability theorem and is the bridge toward the shifted Gaussian Lévy–Khintchine exponent.
-- source:
--   Proved gaussian_compensated_jump_pos_linear; independently published gaussian_compensated_jump_quadratic (awaiting authoritative proof); esscher_tilted_tail_area_integrable.

import Mathlib

theorem AvramDividend.Classical.gaussian_esscher_compensator_envelope
    (φ θ z : ℝ) (hφ : 0 < φ) (hθ : 0 ≤ θ) (hz : 0 ≤ z) :
    Real.exp (-φ * z) * (Real.exp (-θ * z) - 1 + θ * z) ≤
      (θ + θ ^ 2) * (Real.exp (-φ * z) * min (z ^ 2) z) := by sorry
