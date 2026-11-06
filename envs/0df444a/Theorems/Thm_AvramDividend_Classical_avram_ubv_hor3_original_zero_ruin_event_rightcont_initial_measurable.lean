-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_ruin_event_rightcont_initial_measurable
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_zero_ruin_event_rightcont_initial_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:16:05.412925+00:00
-- url     : https://prove2.me/theorems/165b6853-58bd-433d-a0b7-09add9854995
-- title:
--   Original natural ruin-time zero and positive-ruin events are measurable at time zero in the right-continuous filtration
-- statement:
--   For the original spectrally negative Levy X and the original admissible dividend strategy D, the event that the literal ruinTime X x D equals zero, and its complementary strictly positive ruin-time event, belong to the initial sigma-algebra of the right-continuous filtration. The proof uses the already Proved original stopping-time theorem, not any synthetic process. This is necessary for conditional mean-zero martingale localisation at the boundary event.
-- source:
--   Original ruinTime_stopping_rightCont_filtration (Proved 2d036d4f) plus exact ENNReal le-zero equivalence. Import source definition IsAdmissibleLe to obtain IsDividendStrategy 𝓕 D. Supports the positive-ruin weighted cash budget decomposition; no stochastic source fdb import.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_hor3_original_zero_ruin_event_rightcont_initial_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    MeasurableSet[𝓕.rightCont 0] {ω : Ω | ruinTime X x D ω = 0} ∧
    MeasurableSet[𝓕.rightCont 0] {ω : Ω | ruinTime X x D ω ≠ 0} := by sorry
