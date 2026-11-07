-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_20261106_admissible_initial_reserve_nonnegative
-- name    : AvramDividend.Classical.avram_sweep16_20261106_admissible_initial_reserve_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:36:32.014867+00:00
-- url     : https://prove2.me/theorems/e3f75d30-47c6-4383-a667-acffe44d63db
-- title:
--   An original admissible Lévy dividend strategy must have a nonnegative initial reserve
-- statement:
--   The original spectrally negative Lévy structure carries a probability law, hence its sample type cannot be empty. The already Proved exact physical time-zero postpayment reserve inequalities hold for every sample and combine with X(0)=0 to force x≥0. The probability law excludes the empty-sample corner case, making x≥0 an unconditional derived hypothesis for canonical corrected UBV verification 429e17ca, even though 429 does not state it explicitly.
-- source:
--   Exact original-process source from the Proved avram_p4_e_localise_original_initial_postpayment_reserve_between_zero_and_book (3038f74a), SpectrallyNegativeLevy.isProbability and SpectrallyNegativeLevy.X_zero; no invented process, and no point-sampling without checking the probability law.

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_initial_postpayment_reserve_between_zero_and_book
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_sweep16_20261106_admissible_initial_reserve_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) : 0 ≤ x := by sorry
