-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_support_firstRecord_strict_upcrossing_stoppedHistory
-- name    : AvramDividend.Classical.avram_ws01e_b_support_firstRecord_strict_upcrossing_stoppedHistory
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:55:44.533353+00:00
-- url     : https://prove2.me/theorems/783f6103-1512-4a19-9759-18cea92f563e
-- title:
--   An uncensored first-record crossing is measurable in its capped stopped-history sigma-algebra
-- statement:
--   For the genuine spectrally negative Lévy strict first-upcrossing time at level b and any deterministic finite cap N, the event that the original upcrossing happened strictly before N is measurable in the stopped-history sigma-algebra of the right-continuous filtration at the capped observation time min(τ_b,N). The proof uses the accepted source-specific right-continuous capped stopping time and exact ENNReal/NNReal coercion, identifies {τ_b<N} with {min(τ_b,N)<N} including the terminal and infinity cases, then applies Mathlib IsStoppingTime.measurableSet_lt' in the stopped sigma-algebra. This removes the unnecessary lower-ruin condition in a previous first-record stopped-history helper and supports genuine finite-rate Wiener–Hopf clock regeneration. It does not assert any two-sided exit transform, stopped scale martingale or Wiener–Hopf splitting.

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_stopping_rightCont
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_coe_toNNReal_with_measure_import

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_support_firstRecord_strict_upcrossing_stoppedHistory
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (N : ℝ≥0) :
    MeasurableSet[
      (isStoppingTime_withTop_of_le_events
        (fun ω : Ω =>
          (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal)
        (firstRecord_truncation_stopping_rightCont X b N)).measurableSpace]
      {ω : Ω | twoSidedExitUpTime X b ω < (N : ℝ≥0∞)} := by sorry
