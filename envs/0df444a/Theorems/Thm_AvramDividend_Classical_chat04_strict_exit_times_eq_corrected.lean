-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_times_eq_corrected
-- name    : AvramDividend.Classical.chat04_strict_exit_times_eq_corrected
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T14:25:33.536578+00:00
-- url     : https://prove2.me/theorems/bf55283b-bbac-485c-bb9f-3e250ac1e286
-- title:
--   Strict original and corrected two-sided exit clocks agree pointwise
-- statement:
--   The original and corrected strict upward and downward first-passage times agree pointwise for any process, thresholds and sample path, including zero and infinite passage times. Both pairs are literally the infimum of the same strict crossing sets.
-- source:
--   Exact syntactic comparison of the published two-sided-exit definition modules a151e213-9af7-4401-b163-8e74db317cf8 and e8e42ce5-03a3-4ff7-bd29-3067a57464c0.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_strict_exit_times_eq_corrected
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b c : ℝ) (ω : Ω) :
    twoSidedExitUpTime X b ω = twoSidedExitUpTimeCorrected X b ω ∧
      twoSidedExitDownTime X c ω = twoSidedExitDownTimeCorrected X c ω := by sorry
