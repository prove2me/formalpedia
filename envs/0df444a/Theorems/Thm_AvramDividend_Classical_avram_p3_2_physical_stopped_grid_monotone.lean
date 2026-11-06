-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_physical_stopped_grid_monotone
-- name    : AvramDividend.Classical.avram_p3_2_physical_stopped_grid_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:52:20.35374+00:00
-- url     : https://prove2.me/theorems/3a58db8b-ea54-4876-b9fe-c2cbd534b9d1
-- title:
--   Actual clipped physical uniform stopped grid is monotone
-- statement:
--   The capped uniform physical mesh j↦min(((min j (m+1))*T/(m+1)),τ) in NNReal is monotone, including repeated clipped terminal points.
-- source:
--   Natural-number min monotonicity, cast monotonicity, multiplication by the nonnegative grid width, and outer min monotonicity.

import Mathlib

open scoped NNReal

theorem AvramDividend.Classical.avram_p3_2_physical_stopped_grid_monotone (T τ : ℝ≥0) (m : ℕ) :
    Monotone (fun j : ℕ =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ):= by sorry
