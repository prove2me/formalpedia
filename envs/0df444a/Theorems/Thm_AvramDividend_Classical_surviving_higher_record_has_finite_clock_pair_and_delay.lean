-- Prove2me | Theorems.Thm_AvramDividend_Classical_surviving_higher_record_has_finite_clock_pair_and_delay
-- name    : AvramDividend.Classical.surviving_higher_record_has_finite_clock_pair_and_delay
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:03:54.480511+00:00
-- url     : https://prove2.me/theorems/4cc101b6-13b2-4796-a73d-bdb2c4048024
-- title:
--   Surviving higher record supplies finite adjacent record clocks and delay
-- statement:
--   When the higher of two nonnegative-spaced upper first-passage levels is reached before reflected ruin, the higher time is finite and monotonicity makes the lower time finite. Their extended clocks may therefore be converted to finite NNReal clock values with a nonnegative duration δ satisfying u+δ=v. Supplies the exact finite-record witnesses needed by the stopped-renewal upper bound.
-- source:
--   Use the strict survival inequality to rule out a top later clock, monotonicity to rule out top at the earlier level, convert using ENNReal.coe_toNNReal, and apply the finite-clock nonnegative-delay theorem.

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_mono_threshold

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.surviving_higher_record_has_finite_clock_pair_and_delay
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (a b ε : ℝ) (hε : 0 ≤ ε)
    (hSurvive : twoSidedExitUpTime X (b + ε) ω <
      barrierRuinTime X a ω) :
    ∃ u v δ : ℝ≥0,
      (u : ℝ≥0∞) = twoSidedExitUpTime X b ω ∧
      (v : ℝ≥0∞) = twoSidedExitUpTime X (b + ε) ω ∧
      u + δ = v := by sorry
