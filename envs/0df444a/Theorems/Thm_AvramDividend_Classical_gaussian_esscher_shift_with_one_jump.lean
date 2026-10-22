-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_shift_with_one_jump
-- name    : AvramDividend.Classical.gaussian_esscher_shift_with_one_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T07:47:34.956249+00:00
-- url     : https://prove2.me/theorems/1346efd4-1556-4c47-b466-08450112e7ea
-- title:
--   Exact Gaussian-plus-truncated-single-jump Lévy Esscher shift
-- statement:
--   For arbitrary real drift b, Gaussian coefficient a, Esscher base φ, Laplace increment θ, jump size z and truncation term k, the shift of bλ+aλ² plus a single-jump Lévy compensator exactly splits into θ times the modified drift, Gaussian quadratic term aθ² and the Esscher-damped quadratic jump compensator. Combine the already Proved gaussian_levy_esscher_shift_algebra with elementary Gaussian polynomial algebra. This is a source-faithful scalar precursor to integrating the full shifted Lévy–Khintchine formula.
-- source:
--   Proved gaussian_levy_esscher_shift_algebra; pinned ring tactic.

import Mathlib

theorem AvramDividend.Classical.gaussian_esscher_shift_with_one_jump (b a φ θ z k : ℝ) :
    (b * (φ + θ) + a * (φ + θ) ^ 2 +
        (Real.exp (-(φ + θ) * z) - 1 + (φ + θ) * k)) -
      (b * φ + a * φ ^ 2 +
        (Real.exp (-φ * z) - 1 + φ * k)) =
      θ * (b + 2 * a * φ + k - z * Real.exp (-φ * z)) +
        a * θ ^ 2 +
          Real.exp (-φ * z) * (Real.exp (-θ * z) - 1 + θ * z) := by sorry
