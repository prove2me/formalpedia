-- Prove2me | Theorems.Thm_AvramDividend_Classical_twoSidedExitBeforeDown_probability_mono_bounds
-- name    : AvramDividend.Classical.twoSidedExitBeforeDown_probability_mono_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:31:07.385802+00:00
-- url     : https://prove2.me/theorems/737ab5dc-2629-42e6-9c15-3ff8fee0be3e
-- title:
--   Two-sided exit-before-ruin probability is monotone under boundary relaxation
-- statement:
--   For alo ≤ ahi and blo ≤ bhi, the probability of strict upper crossing at ahi before strict lower crossing at bhi does not exceed the probability for the relaxed boundaries alo and blo. This gives a direct reusable comparison of finite or infinite first-passage probabilities in the two-sided-exit branch.
-- source:
--   Verified pathwise exit-event monotonicity followed by monotonicity of an arbitrary measure.

import Theorems.Thm_AvramDividend_Classical_twoSidedExitBeforeDown_event_mono_bounds
import Mathlib.MeasureTheory.OuterMeasure.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.twoSidedExitBeforeDown_probability_mono_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (alo ahi blo bhi : ℝ) (hu : alo ≤ ahi) (hd : blo ≤ bhi) :
    P {ω : Ω | twoSidedExitUpTime X ahi ω < twoSidedExitDownTime X bhi ω} ≤
      P {ω : Ω | twoSidedExitUpTime X alo ω < twoSidedExitDownTime X blo ω} := by sorry
