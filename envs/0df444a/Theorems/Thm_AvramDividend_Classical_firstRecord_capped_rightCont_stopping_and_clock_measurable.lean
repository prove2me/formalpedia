-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstRecord_capped_rightCont_stopping_and_clock_measurable
-- name    : AvramDividend.Classical.firstRecord_capped_rightCont_stopping_and_clock_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:46:13.858179+00:00
-- url     : https://prove2.me/theorems/aca9a992-5fd8-4eae-826e-414a8ca54ee9
-- title:
--   Capped record clock satisfies both stopped Markov measurability requirements
-- statement:
--   A finite cap of a strict first-upcrossing record gives a real-valued right-continuous-filtration stopping time whose random clock is measurable. Both facts are exposed together for use as the two stopping-clock hypotheses in the finite stopped Markov factorisation.
-- source:
--   Proved firstRecord_truncation_stopping_rightCont and firstRecord_truncation_clock_measurable.

import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_stopping_rightCont
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_clock_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.firstRecord_capped_rightCont_stopping_and_clock_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (N : ℝ≥0) :
    (let τ : Ω → ℝ≥0 := fun ω =>
      (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     (∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s}) ∧
       Measurable τ) := by sorry
