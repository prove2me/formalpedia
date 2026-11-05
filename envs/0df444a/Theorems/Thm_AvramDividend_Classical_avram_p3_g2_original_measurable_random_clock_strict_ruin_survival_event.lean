-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_measurable_random_clock_strict_ruin_survival_event
-- name    : AvramDividend.Classical.avram_p3_g2_original_measurable_random_clock_strict_ruin_survival_event
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:31:22.191204+00:00
-- url     : https://prove2.me/theorems/f0d305a1-2cee-4058-994c-a31f328bd1b3
-- title:
--   Original strict random-clock pre-ruin survival event is measurable without stopping-time assumption
-- statement:
--   For the actual controlled spectrally negative Levy reserve, comparison of any measurable nonnegative real clock with the measurable original ENNReal ruin time forms a measurable strict survival event. No independent copy or stopping-time condition is involved; the strict inequality excludes a ruin jump at the observation time.
-- source:
--   Proved/public original ruinTime_measurable bbfbecf4 and pinned Mathlib measurable_coe_nnreal_ennreal_iff.mpr and measurableSet_lt. Discharges hSurvivalMeas of fifth G2 random-clock preterminal L1 bridge.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g2_original_measurable_random_clock_strict_ruin_survival_event
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0) (hτMeas : Measurable τ) :
    MeasurableSet {ω : Ω |
      (τ ω : ℝ≥0∞) < ruinTime X x D ω} := by sorry
