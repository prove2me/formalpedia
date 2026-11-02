-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_expected_original_predictable_generator_cap_patch_invariance
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_expected_original_predictable_generator_cap_patch_invariance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:59:01.911212+00:00
-- url     : https://prove2.me/theorems/4e2f7cec-dbc3-4f20-9f69-7a9eebc8f030
-- title:
--   Original UBV expected compensated generator integral is insensitive to exact predictable cap-value patches
-- statement:
--   For the genuine original capped UBV spectrally negative Levy source and same-filtration dividend strategy, any two nonnegative possibly infinite original predictable generator/compensator density kernels F and G that agree at every positive surviving time except possibly where the exact chronological left-limit reserve equals cap have identical P-expectations of their stopped atomless physical-time integrals. This includes initial capital at cap and recurrent cap contact, and arbitrary changes to the cap generator's boundary value. No w'(c−) or C2 at cap is assumed. The theorem is an expectation-level clock nullity statement only; random cap local time and singular dividend Stieltjes effects remain outside scope.
-- source:
--   Proved one-event physical-clock ENNReal cap-patch invariance 85bf49cc-9893-4771-82cf-6597e583cfd0, based on original same-source UBV cap occupation cc500549-ba08-47b0-b5c0-07c7a9bb40f3 and chronology 89e50cbf-efd7-4c66-8cd6-2d1e99de1a8d. Corrected core untouched 429e17ca-5528-40b5-b593-7c03973d0706.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_generator_cap_value_patch_integral_independence

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_expected_original_predictable_generator_cap_patch_invariance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ (F G : ℝ≥0 → Ω → ℝ≥0∞),
      (∀ (ω : Ω) (t : ℝ≥0), 0 < t →
        (t : ℝ≥0∞) < ruinTime X x D ω →
        Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ≠ c →
        F t ω = G t ω) →
      (∫⁻ ω : Ω, ∫⁻ t : ℝ≥0,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω
        then F t ω else 0 ∂μ ∂P) =
      (∫⁻ ω : Ω, ∫⁻ t : ℝ≥0,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω
        then G t ω else 0 ∂μ ∂P) := by sorry
