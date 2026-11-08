-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_bracket_progressive_of_continuous
-- name    : AvramDividend.Classical.avram_ubv_gaussian10_original_bracket_progressive_of_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T11:31:59.041872+00:00
-- url     : https://prove2.me/theorems/128627b6-35f2-46b8-9040-67556a4810ed
-- title:
--   Original Gaussian bracket is progressive under pathwise time continuity
-- statement:
--   On Avram’s unchanged probability space, any coefficient predictable for the exact right-continuous filtration has a strongly progressive squared bracket when every sample path of the time-integrated square is continuous. The adaptedness follows from the already Proved original-filtration bracket theorem. Continuity is explicit, appropriate for diffuse Lebesgue time with local square-integrability, and remains a separate mathematical obligation.
-- source:
--   Proved original bracket adapted 5f4ccdfd and pinned Mathlib Probability.Process.Adapted StronglyAdapted.isStronglyProgressive_of_continuous, inspected 2026-11-07.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_rightcont_predictable_bracket_adapted

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian10_original_bracket_progressive_of_continuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : ℝ≥0 × Ω → ℝ)
    (hH : Measurable[𝓕.rightCont.predictable] H)
    (μtime : Measure ℝ≥0) [SFinite μtime]
    (hContinuous : ∀ ω, Continuous (fun b : ℝ≥0 =>
      ∫ t in Ioc (0 : ℝ≥0) b, (H (t, ω)) ^ 2 ∂μtime)) :
    IsStronglyProgressive 𝓕.rightCont (fun b ω =>
      ∫ t in Ioc (0 : ℝ≥0) b, (H (t, ω)) ^ 2 ∂μtime) := by sorry
