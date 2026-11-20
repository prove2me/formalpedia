-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_actual_canonical_grid_after_crossing_identically_stopped
-- name    : AvramDividend.Classical.avram_jump6_B_actual_canonical_grid_after_crossing_identically_stopped
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:38:49.582183+00:00
-- url     : https://prove2.me/theorems/89037ce8-0278-4bf8-b47d-d21438129539
-- title:
--   Original physical grid remains exactly at stopped clock after first contact
-- statement:
--   For the exact Jump6 physical grid min(i/(j+1),t), once its value reaches the true stopped time t at any index, every later index equals t. This source-exact fact zeroes all further payment-potential differences after the unique crossing cell.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_actual_canonical_grid_monotone_zero_and_reaches_stop_v2
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_actual_canonical_grid_after_crossing_identically_stopped
    (n j : ℕ) (t : ℝ≥0) (ht : t ≤ (n : ℝ≥0))
    (k : ℕ)
    (hk : min ((k : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t = t) :
    ∀ l : ℕ, k ≤ l →
      min ((l : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t = t := by sorry
