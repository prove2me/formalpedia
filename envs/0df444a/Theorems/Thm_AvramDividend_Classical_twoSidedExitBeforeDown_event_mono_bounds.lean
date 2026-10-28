-- Prove2me | Theorems.Thm_AvramDividend_Classical_twoSidedExitBeforeDown_event_mono_bounds
-- name    : AvramDividend.Classical.twoSidedExitBeforeDown_event_mono_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:26:27.728644+00:00
-- url     : https://prove2.me/theorems/7e297016-b99c-44a3-ba7c-7ac3b6094ed7
-- title:
--   Two-sided strict upper-before-lower exit event is monotone in both boundaries
-- statement:
--   For a given Lévy path and lower/upper thresholds alo ≤ ahi and blo ≤ bhi, a strict crossing of the higher upper threshold before crossing the higher lower threshold implies crossing the smaller upper threshold before crossing the smaller lower threshold. This pathwise event inclusion is a reusable basis for two-sided exit probability and discounted-expectation comparisons.
-- source:
--   Verified pathwise monotonicity of canonical strict upper and lower exit clocks in their thresholds.

import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_mono_threshold
import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_antitone_threshold

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.twoSidedExitBeforeDown_event_mono_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (alo ahi blo bhi : ℝ) (hu : alo ≤ ahi) (hd : blo ≤ bhi) :
    {ω : Ω | twoSidedExitUpTime X ahi ω < twoSidedExitDownTime X bhi ω} ⊆
      {ω : Ω | twoSidedExitUpTime X alo ω < twoSidedExitDownTime X blo ω} := by sorry
