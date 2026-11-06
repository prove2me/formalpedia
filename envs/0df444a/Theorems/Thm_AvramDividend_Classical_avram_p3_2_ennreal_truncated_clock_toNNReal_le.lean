-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_ennreal_truncated_clock_toNNReal_le
-- name    : AvramDividend.Classical.avram_p3_2_ennreal_truncated_clock_toNNReal_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T00:11:06.569252+00:00
-- url     : https://prove2.me/theorems/3a615713-9485-4853-9992-8131994c157e
-- title:
--   Every horizon-truncated extended stopping clock projects into the physical horizon
-- statement:
--   For arbitrary possibly infinite ruin time a and finite NNReal horizon T, the truncated time min(a,T), converted from ENNReal to NNReal, lies below T.
-- source:
--   Pinned Mathlib ENNReal.toNNReal_le_toNNReal with explicit finiteness from a finite upper bound.

import Mathlib

open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_ennreal_truncated_clock_toNNReal_le (a : ℝ≥0∞) (T : ℝ≥0) :
    (min a (T : ℝ≥0∞)).toNNReal ≤ T:= by sorry
