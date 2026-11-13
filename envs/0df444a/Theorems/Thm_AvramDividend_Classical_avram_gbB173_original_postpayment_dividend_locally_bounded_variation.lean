-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB173_original_postpayment_dividend_locally_bounded_variation
-- name    : AvramDividend.Classical.avram_gbB173_original_postpayment_dividend_locally_bounded_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:35:24.364538+00:00
-- url     : https://prove2.me/theorems/af0179e3-45d9-4b0c-8e4d-0daa98a175a7
-- title:
--   Original postpayment dividend right-limit paths have locally bounded variation
-- statement:
--   The postpayment dividend path rightLimit D is monotone by the proved original dividend strategy theorem, hence has locally bounded total variation. This is the exact finite variation component of the postpayment Gaussian reserve used in the local-time occupation route B169.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB173_original_postpayment_dividend_locally_bounded_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    LocallyBoundedVariationOn (fun t : ℝ≥0 => rightLimit D t ω) Set.univ := by sorry
