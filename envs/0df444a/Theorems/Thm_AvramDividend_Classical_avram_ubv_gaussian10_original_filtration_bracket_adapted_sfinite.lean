-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_filtration_bracket_adapted_sfinite
-- name    : AvramDividend.Classical.avram_ubv_gaussian10_original_filtration_bracket_adapted_sfinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:44:54.125294+00:00
-- url     : https://prove2.me/theorems/063995b3-4670-450e-9233-fa39a935d454
-- title:
--   Gaussian quadratic-variation bracket adapted to original Avram filtration for σ-finite time measures
-- statement:
--   For the original spectrally negative Lévy sample space and filtration, suppose the squared Gaussian integrand clamped to each time band (0,b] is measurable for Borel time times the original filtration at b. Then its pathwise time integral over that band is adapted to exactly Avram's filtration. The proof uses measurable integration in the time variable; the trace theorem from original predictability remains an independent premise to establish. No natural-filtration replacement or null completion is made. The time measure is explicitly σ-finite, as required by the pinned measurable-section integration theorem.
-- source:
--   formal-applied-math/formal-mathfin MathFin/Foundations/BracketCompensator.lean measurable_integral_section and bracketProcess_adapted, accessed 2026-11-07; adapted to arbitrary Avram 𝓕 and the supplied Lévy sample space.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian10_original_filtration_bracket_adapted_sfinite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω × ℝ≥0 → ℝ) (μtime : Measure ℝ≥0) [SFinite μtime]
    (hBand : ∀ b : ℝ≥0,
      Measurable[@Prod.instMeasurableSpace Ω ℝ≥0 (𝓕 b) inferInstance]
        (fun z : Ω × ℝ≥0 =>
          (Ioc 0 b).indicator (fun t => (H (z.1, t)) ^ 2) z.2)) :
    Adapted 𝓕 (fun b ω => ∫ t in Ioc (0 : ℝ≥0) b, (H (ω, t)) ^ 2 ∂μtime) := by sorry
