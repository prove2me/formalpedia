-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB39_interior_finite_cap_fraction_strict_band
-- name    : AvramDividend.Classical.avram_gbB39_interior_finite_cap_fraction_strict_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:38:46.080113+00:00
-- url     : https://prove2.me/theorems/98f9e859-1bef-43b2-b8b3-75ab89408390
-- title:
--   Original finite-cap rational interior clipping levels are strictly between zero and cap
-- statement:
--   For any positive real finite cap c and natural stage j, the interior clipping level b_j=c(j+1)/(j+2) is strictly positive and strictly below c, ensuring clipping occurs inside the open C2 reserve band rather than at its regularity boundary.
-- source:
--   Positive real ratio and strict numerator-denominator inequality; used with ENNReal.toReal_pos on original finite cap.

import Mathlib
open Set
noncomputable section

theorem AvramDividend.Classical.avram_gbB39_interior_finite_cap_fraction_strict_band
    (c : ℝ) (hc : 0 < c) (j : ℕ) :
    let b : ℝ := c * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    0 < b ∧ b < c := by sorry
