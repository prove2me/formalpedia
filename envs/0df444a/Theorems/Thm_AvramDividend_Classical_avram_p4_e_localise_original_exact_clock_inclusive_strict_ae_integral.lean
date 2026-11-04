-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_exact_clock_inclusive_strict_ae_integral
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_exact_clock_inclusive_strict_ae_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:10:20.205607+00:00
-- url     : https://prove2.me/theorems/2674a3a0-7b07-4cf1-8fa1-ae4626ee0802
-- title:
--   Actual ruin-truncated source clock inclusive endpoints agree with strict physical-time integral
-- statement:
--   For every original process and path, finite true clock min(ruinTime,n), and any deterministic physical-time measure with NullSingletonClass, the inclusive interval [0,τ] and strict interior (0,τ) produce ae equal zero-extended integrands and identical real integrals. This holds for arbitrary signed f without integrability assumptions because Lebesgue integrals respect a.e. equality. It does not apply to dividendMeasure D ω, which may carry atoms.
-- source:
--   Original ruinTime and canonical clipped ENNReal clock; pinned Mathlib μ.ae_ne and integral_congr_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original ruin-truncated clock endpoints have zero physical-time measure. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_exact_clock_inclusive_strict_ae_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (μ : Measure ℝ≥0) [NullSingletonClass μ]
    (f : ℝ≥0 → ℝ) (ω : Ω) :
    (fun t : ℝ≥0 => if t ≤ (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal then f t else 0)
      =ᵐ[μ] (fun t : ℝ≥0 => if 0 < t ∧ t < (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal then f t else 0) ∧
    (∫ t : ℝ≥0, if t ≤ (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal then f t else 0 ∂μ) =
      (∫ t : ℝ≥0, if 0 < t ∧ t < (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal then f t else 0 ∂μ) := by sorry
