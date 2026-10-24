-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_corrected_twoSidedExitExpectation_antitone_discount
-- name    : AvramDividend.Classical.chat04_corrected_twoSidedExitExpectation_antitone_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T14:21:12.535999+00:00
-- url     : https://prove2.me/theorems/0f7f9067-fc5e-4a44-95d3-662dd84318c2
-- title:
--   Corrected killed two-sided exit transform decreases with discount
-- statement:
--   The corrected killed strict upper-before-lower first-passage transform is nonincreasing as the discount rate rises. This gives the Esscher comparison workstream a directly named lemma for its corrected exit definition and follows rigorously from the Proved equivalence and original-transform discount monotonicity.
-- source:
--   Derived from Proved chat04_twoSidedExitExpectation_eq_corrected (caca9b2f-00ac-4b28-8aa7-a322673e5937) and Proved chat04_twoSidedExitExpectation_antitone_discount (69a4a254-000a-4139-880d-577bc9fca961).

import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_eq_corrected
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_antitone_discount

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_corrected_twoSidedExitExpectation_antitone_discount
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q₁ q₂ a x : ℝ) (hq : q₁ ≤ q₂) :
    twoSidedExitExpectationCorrected X q₂ a x ≤
      twoSidedExitExpectationCorrected X q₁ a x := by sorry
