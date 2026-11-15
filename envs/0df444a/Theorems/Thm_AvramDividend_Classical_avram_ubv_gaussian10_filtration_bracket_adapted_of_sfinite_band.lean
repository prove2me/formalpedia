-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_filtration_bracket_adapted_of_sfinite_band
-- name    : AvramDividend.Classical.avram_ubv_gaussian10_filtration_bracket_adapted_of_sfinite_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:44:29.672067+00:00
-- url     : https://prove2.me/theorems/2443ffc9-7dca-4940-be75-27ed34977634
-- title:
--   Adapted stopped quadratic bracket from jointly measurable band and s-finite time measure
-- statement:
--   The time-integrated square bracket of a bandwise product measurable integrand is filtration-adapted if the time measure is s-finite. The s-finite hypothesis permits the measurable parameter-integral theorem for Bochner integrals. This repairs the original formulation, which quantified over arbitrary (possibly non-s-finite) measures.
-- source:
--   Pinned Mathlib MeasureTheory.StronglyMeasurable.integral_prod_right; corrected UBV Gaussian predictable-bracket measurability

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian10_filtration_bracket_adapted_of_sfinite_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω × ℝ≥0 → ℝ) (μtime : Measure ℝ≥0) [SFinite μtime]
    (hBand : ∀ b : ℝ≥0,
      Measurable[@Prod.instMeasurableSpace Ω ℝ≥0 (𝓕 b) inferInstance]
        (fun z : Ω × ℝ≥0 =>
          (Ioc 0 b).indicator (fun t => (H (z.1, t)) ^ 2) z.2)) :
    Adapted 𝓕 (fun b ω => ∫ t in Ioc (0 : ℝ≥0) b, (H (ω, t)) ^ 2 ∂μtime) := by sorry
