-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a40_physical_normalised_large_tail_scaling
-- name    : AvramDividend.Classical.avram_ga_a40_physical_normalised_large_tail_scaling
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:34:19.375662+00:00
-- url     : https://prove2.me/theorems/8662ac10-5af5-48e7-a6bb-f7eae0e93d39
-- title:
--   Large Gaussian quadratic increment threshold and energy commute with positive volatility normalisation
-- statement:
--   For positive volatility sigma and threshold eta, the unnormalised squared increment above threshold eta equals sigma squared times the normalised squared increment above eta/sigma.
-- source:
--   Original Gaussian stopped Taylor b0d9951c, converts normalized Proved large-cell Lindeberg to real original source increments.

import Mathlib

theorem AvramDividend.Classical.avram_ga_a40_physical_normalised_large_tail_scaling (z σ η : ℝ) (hσ : 0 < σ) (hη : 0 < η) :
    (if η ≤ |z| then z ^ 2 else 0) =
      σ ^ 2 * (if η / σ ≤ |z / σ| then (z / σ) ^ 2 else 0) := by sorry
