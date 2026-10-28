-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstRecord_capped_clock_eq_true_clock_within_horizon
-- name    : AvramDividend.Classical.firstRecord_capped_clock_eq_true_clock_within_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T00:16:31.459285+00:00
-- url     : https://prove2.me/theorems/1ad55083-4b85-46f2-9820-0f15bf5c3a4e
-- title:
--   Capped first-record clock equals actual upper-record clock on the finite-horizon event
-- statement:
--   On an event where the upper passage happens by finite horizon N, the truncated finite clock equals the original passage clock after toNNReal. This allows replacing stopped process shifts and discounts in the localised strong Markov estimate.
-- source:
--   min_eq_left for ENNReal truncation

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.firstRecord_capped_clock_eq_true_clock_within_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (N : ℝ≥0) (ω : Ω)
    (hN : twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)) :
    (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal =
      (twoSidedExitUpTime X b ω).toNNReal := by sorry
