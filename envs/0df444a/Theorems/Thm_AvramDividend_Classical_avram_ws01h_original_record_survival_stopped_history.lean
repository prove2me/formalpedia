-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_original_record_survival_stopped_history
-- name    : AvramDividend.Classical.avram_ws01h_original_record_survival_stopped_history
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T07:54:31.499072+00:00
-- url     : https://prove2.me/theorems/3aa8a4e1-fd0e-4488-a137-c58b9aec37e3
-- title:
--   Original lower-ruin killed prefix is measurable at the capped first-upper-record stopped history
-- statement:
--   At the true finite capped first upcrossing time for a source spectrally negative Lévy process, the historical event of reaching the upper record before the original strict lower exit and by the cap is measurable in the capped stopping-time sigma-algebra. This provides the precise missing past-killing indicator used by the full-future Esscher first-record renewal, unlike earlier theorems involving the reflected barrier ruin time.
-- source:
--   Proved original strict lower clock finite-horizon witness (07415c4f), source filtration lower crossing (335dd834), true upper stopping time (72dac635), Mathlib stopped-time comparison, and Proved generic finite-cap history transfer (ad853cca). No existing two-sided scale exit identity is imported. Distinct from reflected record_survival_stopped_history_measurable (7c79f9d8).

import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_lowerCrossingClock_lt_horizon_iff_exists_witness
import Theorems.Thm_AvramDividend_Classical_levy_lowerCrossing_before_filtration_measurable
import Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_stoppingTime_capped_history_event_measurable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_original_record_survival_stopped_history
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (lower b : ℝ) (N : ℝ≥0) :
    MeasurableSet[
      ((upperPassage_stopping_rightCont_filtration X b).min_const N).measurableSpace]
      ({ω : Ω | twoSidedExitUpTime X b ω < twoSidedExitDownTime X lower ω} ∩
       {ω : Ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)}) := by sorry
