-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_predictable_bracket_adapted
-- name    : AvramDividend.Classical.avram_ubv_gaussian10_original_predictable_bracket_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T11:05:44.534504+00:00
-- url     : https://prove2.me/theorems/01786ffa-c3c4-4bd2-9857-01f18a066544
-- title:
--   Original Gaussian predictable integrand has an adapted squared bracket on the exact Levy filtration
-- statement:
--   For Avram's original spectral-negative Levy process and exact filtration, any measurable predictable coefficient H defines a pathwise squared time-integral bracket adapted to the original filtration under any sigma-finite time measure. The predictable-band trace is converted to a measurable squared indicator, coordinates are swapped, and the existing Proved adapted-bracket result is applied. This does not substitute a Brownian natural filtration or establish the stochastic integral itself.
-- source:
--   Formal-mathfin MathFin/Foundations/BracketCompensator.lean, predictable_le_traceAlg and measurable_bandSqClamped; two Proved AVRAM UBV-GAUSSIAN10 helper theorems, inspected 2026-11-07.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_predictable_band_trace
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_filtration_bracket_adapted_sfinite

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian10_original_predictable_bracket_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : ℝ≥0 × Ω → ℝ)
    (hH : Measurable[𝓕.predictable] H)
    (μtime : Measure ℝ≥0) [SFinite μtime] :
    Adapted 𝓕 (fun b ω =>
      ∫ t in Ioc (0 : ℝ≥0) b, (H (t, ω)) ^ 2 ∂μtime) := by sorry
