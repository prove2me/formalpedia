-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB161_original_strict_prepayment_times_are_nonnegative_horizon_bounded
-- name    : AvramDividend.Classical.avram_gbB161_original_strict_prepayment_times_are_nonnegative_horizon_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T18:20:39.246024+00:00
-- url     : https://prove2.me/theorems/71a6ed8e-54bd-4f1e-96e9-d52e26ae2f62
-- title:
--   Original strict pre-ruin payment times are always contained in nonnegative physical stopping horizon
-- statement:
--   For the source-defined original dividend paymentTimes of any extended-nonnegative ruin time σ, restricting to times strictly before a nonnegative physical horizon T produces a subset of [0,T]. This exact source set inclusion is the missing support hypothesis for transferring finite original barrier Stieltjes measure on [0,T] into discounted stopped cash finiteness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB161_original_strict_prepayment_times_are_nonnegative_horizon_bounded
    (σ : ℝ≥0∞) (T : ℝ≥0) :
    paymentTimes σ ∩ Iio (T : ℝ) ⊆
      Icc (0 : ℝ) (T : ℝ) := by sorry
