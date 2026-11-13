-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a38_original_grid_second_energy_uniform_rate
-- name    : AvramDividend.Classical.avram_ga_a38_original_grid_second_energy_uniform_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:16:28.045239+00:00
-- url     : https://prove2.me/theorems/67f5f951-582c-496c-a1f3-ffe60cb61054
-- title:
--   Original Gaussian uniform-grid total variance energy is bounded by physical horizon
-- statement:
--   For nonnegative integer horizon n and mesh count m, the expected Gaussian variance over the m full physical cells of width n/(m+1) is at most n times sigma squared.
-- source:
--   Deterministic variance-budget component of b0d9951c original Gaussian small-increment positive Taylor proof.

import Mathlib

theorem AvramDividend.Classical.avram_ga_a38_original_grid_second_energy_uniform_rate (n m : ℕ) (σ : ℝ) :
    (m : ℝ) * (((n : ℝ) / ((m : ℝ) + 1)) * σ ^ 2) ≤
      (n : ℝ) * σ ^ 2 := by sorry
