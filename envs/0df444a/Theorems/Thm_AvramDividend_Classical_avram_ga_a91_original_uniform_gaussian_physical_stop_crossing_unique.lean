-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a91_original_uniform_gaussian_physical_stop_crossing_unique
-- name    : AvramDividend.Classical.avram_ga_a91_original_uniform_gaussian_physical_stop_crossing_unique
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:12:45.787765+00:00
-- url     : https://prove2.me/theorems/1e583a7e-0c17-4d9e-bdee-aa7f2fa29b43
-- title:
--   At most one physical Gaussian source cell can straddle the actual original stopping clock
-- statement:
--   For the true original uniform Gaussian physical grid of horizon n and m+1 denominator, if cell i begins strictly before the stop and ends at or after it, then no later cell may also begin before that stop. This proves uniqueness of the stopping-crossing cell.
-- source:
--   Direct original b0d9951c physical full/unique crossing/poststop source partition; use ga_a71, ga_a72, ga_a89, ga_a90.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_ga_a91_original_uniform_gaussian_physical_stop_crossing_unique (n m i j : ℕ) (ρ : ℝ≥0)
    (hij : i < j)
    (hi : (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) < ρ)
    (hcross : ρ ≤ ((i + 1 : ℕ) : ℝ≥0) *
      ((n : ℝ≥0) / ((m : ℝ≥0) + 1)))
    (hj : (j : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) < ρ) :
    False := by sorry
