-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_expected_predictable_signed_generator_cap_patch_invariance
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_expected_predictable_signed_generator_cap_patch_invariance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:01:07.004919+00:00
-- url     : https://prove2.me/theorems/448f9027-2496-4255-96e4-daaaec7a3de1
-- title:
--   Expected signed original predictable generator drift ignores arbitrary exact-cap boundary value patches
-- statement:
--   For the original controlled unbounded-variation spectrally negative Levy source and its true chronological predictable pre-event reserve, any real signed generator/discounted-drift kernels agreeing off exact cap contact at all positive surviving times have identical original law P-expectations of their stopped physical-clock Bochner integrals. Generator boundary values may be patched arbitrarily at U−=c without changing the expected signed drift, even when capital initially equals c and recurrent cap hits occur, because the fixed s-finite atomless time clock ignores cap. This does not prove full stochastic Itô–Meyer, stochastic martingale expectation passage, or singular local-time/Stieltjes clock nullity.
-- source:
--   Proved signed pathwise original predictable generator patch independence 8f396098-41fd-43c0-a1ec-5b4f1967ebb1, original cap occupation cc500549-ba08-47b0-b5c0-07c7a9bb40f3, chronology 89e50cbf-efd7-4c66-8cd6-2d1e99de1a8d. Corrected canonical core 429e17ca-5528-40b5-b593-7c03973d0706 unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_signed_generator_cap_value_patch_integral_independence

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_expected_predictable_signed_generator_cap_patch_invariance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ (F G : ℝ≥0 → Ω → ℝ),
      (∀ (ω : Ω) (t : ℝ≥0), 0 < t →
        (t : ℝ≥0∞) < ruinTime X x D ω →
        Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ≠ c →
        F t ω = G t ω) →
      (∫ ω : Ω, ∫ t : ℝ≥0,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω
        then F t ω else 0 ∂μ ∂P) =
      (∫ ω : Ω, ∫ t : ℝ≥0,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω
        then G t ω else 0 ∂μ ∂P) := by sorry
