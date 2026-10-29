-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_raw_strict_lower_clock_le_grid_cap_ws01c
-- name    : AvramDividend.Classical.bv_raw_strict_lower_clock_le_grid_cap_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T22:45:10.212211+00:00
-- url     : https://prove2.me/theorems/5c693569-372c-446a-b224-42cea60c1c5d
-- title:
--   Raw strict lower first-passage clock is below every capped finite grid clock
-- statement:
--   Every sampled strict lower observation lies among the times defining the raw strict first-passage infimum. Therefore the raw clock capped at T is no later than any finite-grid approximant capped at T. This proves the necessary from-above inequality for right-continuous post-clock increments without assuming the raw time is an original-filtration stopping time.
-- source:
--   Existing complete source work/avram_ws01c_strict_raw_clock_below_each_grid_cap_draft.lean, isolated as original necessary right-approximation interface. No new auto-split decomposition. Exact solution work/avram_ws01c_raw_clock_le_grid_cap_solution_20261028.lean.

import Mathlib

open Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_raw_strict_lower_clock_le_grid_cap_ws01c
    (Y : ℝ≥0 → ℝ) (lower : ℝ)
    (h T : ℝ≥0) (M : ℕ) :
    ((⨅ (t : ℝ≥0) (_ : Y t < lower), (t : ℝ≥0∞)) ⊓
      (T : ℝ≥0∞)) ≤
    ((⨅ (k : ℕ) (_ : k ≤ M),
        if Y ((k : ℝ≥0) * h) < lower then
          (((k : ℝ≥0) * h) : ℝ≥0∞) else ⊤) ⊓
        (T : ℝ≥0∞)) := by sorry
