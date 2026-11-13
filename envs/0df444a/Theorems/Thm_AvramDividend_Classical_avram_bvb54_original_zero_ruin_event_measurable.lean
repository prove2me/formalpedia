-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb54_original_zero_ruin_event_measurable
-- name    : AvramDividend.Classical.avram_bvb54_original_zero_ruin_event_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T21:41:12.187191+00:00
-- url     : https://prove2.me/theorems/68fcebd6-3ef0-4ca8-8a3b-339d95953808
-- title:
--   The actual original BV controlled process zero-ruin event is measurable
-- statement:
--   The event that the actual original controlled surplus has ruinTime exactly zero is measurable in the original ambient probability space, under the source admissibility hypotheses. Apply the already Proved original right-continuous filtration stopping-time theorem for the exact ruinTime and pinned Mathlib IsStoppingTime.measurable, then the measurableSet_eq theorem for the constant zero. This directly supplies the zero-ruin mask measurability required by bvb53 and the original phys36d dominated-convergence source residual, without any surrogate process or added path regularity.
-- source:
--   Proved avram_wave4_03_actual_ruinTime_rightCont_stopping_time and pinned Mathlib IsStoppingTime.measurable, measurableSet_eq.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actual_ruinTime_rightCont_stopping_time
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb54_original_zero_ruin_event_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) :
    MeasurableSet {ω : Ω | ruinTime X x D ω = 0} := by sorry
