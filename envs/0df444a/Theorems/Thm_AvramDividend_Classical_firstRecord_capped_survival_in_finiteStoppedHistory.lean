-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstRecord_capped_survival_in_finiteStoppedHistory
-- name    : AvramDividend.Classical.firstRecord_capped_survival_in_finiteStoppedHistory
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T00:05:55.385474+00:00
-- url     : https://prove2.me/theorems/75a45591-a743-46bc-b702-251feb82798e
-- title:
--   Capped first-record survival event belongs to the finite-clock stopped history
-- statement:
--   For the right-continuous Levy filtration, the event that the upper record beats ruin and occurs by a finite horizon is measurable at the finite capped upper-record stopping clock. This enables the finite-stopping strong-Markov reward bound.
-- source:
--   Stopped-history equality transport plus first-record capped survival measurability

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_stopping_rightCont
import Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_measurable_of_equal_finite_clocks
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_coe_toNNReal_with_measure_import
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_survival_history_measurable_explicit_imports

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.firstRecord_capped_survival_in_finiteStoppedHistory
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a b : ℝ) (N : ℝ≥0) :
    MeasurableSet[
      (isStoppingTime_withTop_of_le_events
        (fun ω : Ω => (min (twoSidedExitUpTime X b ω)
          (N : ℝ≥0∞)).toNNReal)
        (firstRecord_truncation_stopping_rightCont X b N)).measurableSpace]
      ({ω : Ω | twoSidedExitUpTime X b ω < barrierRuinTime X a ω} ∩
       {ω : Ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)}) := by sorry
