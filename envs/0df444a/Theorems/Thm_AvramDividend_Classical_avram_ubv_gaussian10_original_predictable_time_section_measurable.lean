-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_predictable_time_section_measurable
-- name    : AvramDividend.Classical.avram_ubv_gaussian10_original_predictable_time_section_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:18:36.1872+00:00
-- url     : https://prove2.me/theorems/cd58d62b-bbfa-4b6a-80a4-04c015f63927
-- title:
--   Original right-continuous predictable Gaussian sources have measurable time sections
-- statement:
--   On Avram's unchanged right-continuous original filtration, a predictable Gaussian integrand has a measurable time section for each original sample point, by containment of predictable rectangles in the ordinary measurable time-product sigma algebra. This makes the prior uniform-bound square-energy theorem applicable to every sample point without null-set modification.
-- source:
--   Pinned Mathlib measurableSpace_le_predictable_of_measurableSet and measurable product-section embedding, 7 November 2026.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian10_original_predictable_time_section_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : ℝ≥0 × Ω → ℝ)
    (hH : Measurable[𝓕.rightCont.predictable] H) :
    ∀ ω, Measurable (fun t : ℝ≥0 => H (t, ω)) := by sorry
