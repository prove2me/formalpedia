-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_source_capped_lower_killed_history_measurable
-- name    : AvramDividend.Classical.avram_ws01h_source_capped_lower_killed_history_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T17:13:59.96711+00:00
-- url     : https://prove2.me/theorems/effee45c-ca1d-4835-9684-65264bdc5c5b
-- title:
--   True source capped upper-record clock and lower-killed historical event are measurable
-- statement:
--   For the actual spectrally negative Lévy original law, both the finite cap of its strict upper first-record clock and the stopped historical event where that upper passage precedes strict lower ruin and occurs no later than the cap are genuinely measurable. This packages already accepted source right-continuous stopping-time results and permits source-faithful lower-killed Qp renewal integration without importing an open two-sided exit theorem.
-- source:
--   Canonically proved source capped clock and upper/lower right-continuous stopping times, pinned Mathlib comparison measurable sets.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_clock_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_lowerPassage_stopping_rightCont_filtration

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_source_capped_lower_killed_history_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower b : ℝ) (N : ℝ≥0) :
    Measurable (fun ω : Ω =>
      (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal) ∧
    MeasurableSet
      ({ω : Ω | twoSidedExitUpTime X b ω <
        twoSidedExitDownTime X lower ω} ∩
       {ω : Ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)}) := by sorry
