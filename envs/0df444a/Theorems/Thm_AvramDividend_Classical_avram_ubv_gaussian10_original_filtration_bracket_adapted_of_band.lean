-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_filtration_bracket_adapted_of_band
-- name    : AvramDividend.Classical.avram_ubv_gaussian10_original_filtration_bracket_adapted_of_band
-- status  : Open
-- author  : @WillR
-- created : 2026-11-07T10:33:48.119136+00:00
-- url     : https://prove2.me/theorems/32deca76-9e61-4f22-ac5f-ea6444d579f1
-- title:
--   Quadratic-variation bracket adapted in Avram's original filtration from predictable-band measurability
-- statement:
--   For the original spectrally negative Lévy sample space and filtration, suppose the squared Gaussian integrand clamped to each time band (0,b] is measurable for Borel time times the original filtration at b. Then its pathwise time integral over that band is adapted to exactly Avram's filtration. The proof uses measurable integration in the time variable; the trace theorem from original predictability remains an independent premise to establish. No natural-filtration replacement or null completion is made.
-- source:
--   formal-applied-math/formal-mathfin MathFin/Foundations/BracketCompensator.lean measurable_integral_section and bracketProcess_adapted, accessed 2026-11-07; adapted to arbitrary Avram 𝓕 and the supplied Lévy sample space.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian10_original_filtration_bracket_adapted_of_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω × ℝ≥0 → ℝ) (μtime : Measure ℝ≥0)
    (hBand : ∀ b : ℝ≥0,
      Measurable[@Prod.instMeasurableSpace Ω ℝ≥0 (𝓕 b) inferInstance]
        (fun z : Ω × ℝ≥0 =>
          (Ioc 0 b).indicator (fun t => (H (z.1, t)) ^ 2) z.2)) :
    Adapted 𝓕 (fun b ω => ∫ t in Ioc (0 : ℝ≥0) b, (H (ω, t)) ^ 2 ∂μtime) := by sorry
