-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_eq_corrected
-- name    : AvramDividend.Classical.chat04_twoSidedExitExpectation_eq_corrected
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T14:02:56.51732+00:00
-- url     : https://prove2.me/theorems/caca9b2f-00ac-4b28-8aa7-a322673e5937
-- title:
--   Strict killed two-sided exit expectation agrees with corrected definition
-- statement:
--   The published strict two-sided exit transform and its corrected counterpart agree identically for every spectrally negative Lévy process and every real discount, upper barrier and starting reserve. Their definitions share strict upward and downward first-passage infima, the same upward-before-downward event and the same ENNReal lower-integral reward.
-- source:
--   Direct comparison of published Definitions.Def_AvramDividend_Classical_TwoSidedExit (a151e213-9af7-4401-b163-8e74db317cf8) and Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected (e8e42ce5-03a3-4ff7-bd29-3067a57464c0).

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_twoSidedExitExpectation_eq_corrected
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q a x : ℝ) :
    twoSidedExitExpectation X q a x =
      twoSidedExitExpectationCorrected X q a x := by sorry
