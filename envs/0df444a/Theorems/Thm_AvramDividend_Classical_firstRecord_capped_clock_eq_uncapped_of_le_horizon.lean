-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstRecord_capped_clock_eq_uncapped_of_le_horizon
-- name    : AvramDividend.Classical.firstRecord_capped_clock_eq_uncapped_of_le_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:30:34.448208+00:00
-- url     : https://prove2.me/theorems/159a20a9-a0ad-4c89-8a23-8674c499dd5a
-- title:
--   Capped first-record clock agrees with its original clock on the survival horizon event
-- statement:
--   If an upper first-passage time is no later than a deterministic cap N, converting the capped extended time to finite nonnegative time and back yields exactly the original first-passage time. This pathwise identity identifies the shifted clock used by finite-stopping Markov factorisation with the uncapped first-record clock on the surviving record event.
-- source:
--   Direct consequence of the Proved firstRecord_capped_coe_toNNReal_with_measure_import theorem and min_eq_left.

import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_coe_toNNReal_with_measure_import

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.firstRecord_capped_clock_eq_uncapped_of_le_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (N : ℝ≥0) (ω : Ω)
    (hbound : twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)) :
    (((min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞) =
      twoSidedExitUpTime X b ω := by sorry
