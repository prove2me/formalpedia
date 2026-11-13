-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a27_horizon_clipped_endpoint
-- name    : AvramDividend.Classical.avram_ga_a27_horizon_clipped_endpoint
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:33:38.387521+00:00
-- url     : https://prove2.me/theorems/fdfb0b39-5d17-49ee-b566-94ec7ad5fd83
-- title:
--   The final clipped Gaussian grid endpoint equals the horizon on the horizon-boundary event
-- statement:
--   When the stopping time rho is at least the finite horizon n, the clipped grid endpoint v(m+1) equals n exactly, for every mesh size. This is the deterministic algebra needed for the remaining horizon-boundary terminal Gaussian limit.
-- source:
--   Avram Gaussian A27 horizon-boundary analysis

import Mathlib
open scoped NNReal

theorem AvramDividend.Classical.avram_ga_a27_horizon_clipped_endpoint
    (n : ℝ≥0) (m : ℕ) (ρ : ℝ≥0) (hnρ : n ≤ ρ) :
    min (((m + 1 : ℕ) : ℝ≥0) *
      (n / ((m : ℝ≥0) + 1))) ρ = n := by sorry
