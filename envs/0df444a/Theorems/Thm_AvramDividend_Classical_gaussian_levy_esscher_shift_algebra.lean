-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_levy_esscher_shift_algebra
-- name    : AvramDividend.Classical.gaussian_levy_esscher_shift_algebra
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T07:08:21.35598+00:00
-- url     : https://prove2.me/theorems/e0684be8-7ec5-49eb-a7a4-693dec714ae0
-- title:
--   Exact truncated negative-jump Lévy compensator Esscher-shift algebra
-- statement:
--   For arbitrary real φ,θ,z and arbitrary truncation term k, the change in the Lévy exponential compensator exp(−λz)−1+λk between λ=φ and λ=φ+θ equals the Esscher-weighted quadratic compensator exp(−φz)(exp(−θz)−1+θz) plus the explicit linear correction θ(k−z exp(−φz)). Prove this by exponential addition and ring algebra. Choosing k=z for small jumps and zero otherwise gives the standard Lévy–Khintchine truncation split, ready for measure-level integrability arguments.
-- source:
--   Pinned Real.exp_add and ring algebra; no Open theorem dependency.

import Mathlib

theorem AvramDividend.Classical.gaussian_levy_esscher_shift_algebra (φ θ z k : ℝ) :
    (Real.exp (-(φ + θ) * z) - 1 + (φ + θ) * k) -
        (Real.exp (-φ * z) - 1 + φ * k) =
      Real.exp (-φ * z) *
          (Real.exp (-θ * z) - 1 + θ * z) +
        θ * (k - z * Real.exp (-φ * z)) := by sorry
