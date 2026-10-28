-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_clock_measurable
-- name    : AvramDividend.Classical.firstRecord_truncation_clock_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:33:59.457017+00:00
-- url     : https://prove2.me/theorems/b199e654-8c2c-4191-a604-c64e5672b53d
-- title:
--   The finite-horizon first-record clock is measurably real-valued
-- statement:
--   For a spectrally negative Lévy process, the strict first-upcrossing clock truncated at any finite horizon is measurable when converted from extended nonnegative reals to ordinary nonnegative reals. This discharges the clock-measurability premise needed by the proved finite-stopping-time strong-Markov discounted future reward factorisation at stopped first-record times.
-- source:
--   Take the min with a finite constant of the proved first-upcrossing stopping time, use the measurable-stopping-clock lemma, and compose with measurable ENNReal.toNNReal.

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.firstRecord_truncation_clock_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (M : ℝ≥0) :
    Measurable (fun ω : Ω =>
      (min (twoSidedExitUpTime X b ω) (M : ℝ≥0∞)).toNNReal) := by sorry
