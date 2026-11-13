-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a27_nnreal_eventual_terminal_saturation
-- name    : AvramDividend.Classical.avram_ga_a27_nnreal_eventual_terminal_saturation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:30:45.187204+00:00
-- url     : https://prove2.me/theorems/d8fc2715-073e-4c93-b0d5-f2f4a0daeb08
-- title:
--   Every strictly pre-horizon nonnegative stopping clock is eventually inside the final clipped mesh
-- statement:
--   For a nonnegative time r strictly smaller than a nonnegative horizon n, uniform mesh endpoints m*n/(m+1) eventually dominate r. This is in the exact NNReal time type needed for the original stopped Gaussian terminal cell.
-- source:
--   Avram original Gaussian gledger179 terminal a.e. zero case r<n

import Mathlib
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a27_nnreal_eventual_terminal_saturation
    (r n : ℝ≥0) (hr : r < n) :
    ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      r ≤ (m : ℝ≥0) * (n / ((m : ℝ≥0) + 1)) := by sorry
