-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB280_translated_gaussian_inverse_sqrt_cell_integral
-- name    : AvramDividend.Classical.avram_gbB280_translated_gaussian_inverse_sqrt_cell_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T22:41:37.812057+00:00
-- url     : https://prove2.me/theorems/ecf0a423-534f-44b9-8af7-a10d33492dcc
-- title:
--   Gaussian inverse-square-root time integral over any translated physical mesh cell
-- statement:
--   For arbitrary real cell origin s and width delta, the physical-time integral from s to s+delta of the inverse square root elapsed-time kernel (t-s)^(-1/2) is twice sqrt(delta). This is the exact translated-cell version of B262 and is essential when integrating each original Gaussian conditional small-ball probability across an arbitrary finite-cap time-grid cell in B274.

import Mathlib
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_gbB280_translated_gaussian_inverse_sqrt_cell_integral (s δ : ℝ) :
    ∫ t in s..(s + δ), (t - s) ^ (-(1 / 2 : ℝ)) =
      2 * Real.sqrt δ := by sorry
