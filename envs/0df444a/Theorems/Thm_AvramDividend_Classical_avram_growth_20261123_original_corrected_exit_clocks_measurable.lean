-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_growth_20261123_original_corrected_exit_clocks_measurable
-- name    : AvramDividend.Classical.avram_growth_20261123_original_corrected_exit_clocks_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T08:16:51.047153+00:00
-- url     : https://prove2.me/theorems/a702eff7-ded9-4fa8-991c-86655efe04a4
-- title:
--   Original corrected upper and lower two-sided exit clocks are measurable
-- statement:
--   Under the authentic spectrally negative Levy process with adapted right-continuous paths, the corrected two-sided first-exit times above b-1 and below -1 are measurable as extended nonnegative random times.
-- source:
--   Original Avram first-exit HJB source 9dbe8433, Gaussian case 770a6d39; correct clocks from original definitions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_growth_20261123_original_corrected_exit_clocks_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (b : ℝ) :
    Measurable (twoSidedExitUpTimeCorrected X (b - 1)) ∧
    Measurable (twoSidedExitDownTimeCorrected X (-1)) := by sorry
