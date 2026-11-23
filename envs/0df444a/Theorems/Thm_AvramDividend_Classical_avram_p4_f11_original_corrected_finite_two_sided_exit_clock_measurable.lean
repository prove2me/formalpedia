-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f11_original_corrected_finite_two_sided_exit_clock_measurable
-- name    : AvramDividend.Classical.avram_p4_f11_original_corrected_finite_two_sided_exit_clock_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T10:47:33.388351+00:00
-- url     : https://prove2.me/theorems/ea026c53-a144-4ff9-a09e-96b1a0cf1449
-- title:
--   Original corrected two-sided first-exit clock clipped at finite n is measurable
-- statement:
--   For the actual spectrally negative Levy process, the first exit clock formed from min of the two corrected strict upper/lower passage times and a finite deterministic horizon is a measurable extended-nonnegative real-valued random variable. Derived directly from already Proved measurability of both physical corrected clocks and measurability of min. Does not assert the stopping-time property.
-- source:
--   Proved a702eff7 corrected first exit measurability, applied to original Avram finite horizon min clock.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f11_original_corrected_finite_two_sided_exit_clock_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (n : ℕ) :
    Measurable (fun ω : Ω =>
      min (twoSidedExitUpTimeCorrected X (b - 1) ω)
        (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞))) := by sorry
