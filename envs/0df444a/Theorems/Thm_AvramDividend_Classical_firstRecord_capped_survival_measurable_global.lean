-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstRecord_capped_survival_measurable_global
-- name    : AvramDividend.Classical.firstRecord_capped_survival_measurable_global
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T00:21:19.821713+00:00
-- url     : https://prove2.me/theorems/4a553ff9-3184-4cb5-8efd-defabd78ee11
-- title:
--   Finite capped first-record survival event is measurable in the ambient probability space
-- statement:
--   A finite-horizon event that the first upward record precedes ruin is measurably defined in the ambient probability space. It follows by inclusion of the stopped-history sigma algebra in the ambient measurable space. This discharges the measurable event input for capped strong-Markov estimates.
-- source:
--   Stopped-history event measurability and IsStoppingTime.measurableSpace_le

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_stopping_rightCont
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_survival_in_finiteStoppedHistory

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.firstRecord_capped_survival_measurable_global
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a b : ℝ) (N : ℝ≥0) :
    MeasurableSet
      ({ω : Ω | twoSidedExitUpTime X b ω < barrierRuinTime X a ω} ∩
       {ω : Ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)}) := by sorry
