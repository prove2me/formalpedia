-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a26_clipped_last_times_equal_after_stop
-- name    : AvramDividend.Classical.avram_ga_a26_clipped_last_times_equal_after_stop
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:04:30.47078+00:00
-- url     : https://prove2.me/theorems/493bafcb-0fad-4c72-bbfc-6fecdb4b44a5
-- title:
--   Adjacent clipped mesh times are equal once the stopping time precedes the final active mesh cell
-- statement:
--   When a stop r is at or before grid point m n/(m+1), both clipped grid times at indices m and m+1 equal r. Supports the original-process terminal Gaussian spatial estimate.
-- source:
--   Avram Gaussian A26 last-cell analysis

import Mathlib
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ga_a26_clipped_last_times_equal_after_stop
    (n : ℝ≥0) (m : ℕ) (r : ℝ≥0)
    (hstop : r ≤ (m : ℝ≥0) * (n / ((m : ℝ≥0) + 1))) :
    min ((m : ℝ≥0) * (n / ((m : ℝ≥0) + 1))) r = r ∧
    min (((m + 1 : ℕ) : ℝ≥0) * (n / ((m : ℝ≥0) + 1))) r = r := by sorry
