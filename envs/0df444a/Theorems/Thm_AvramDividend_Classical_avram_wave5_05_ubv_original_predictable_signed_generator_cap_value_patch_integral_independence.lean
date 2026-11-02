-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_signed_generator_cap_value_patch_integral_independence
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_signed_generator_cap_value_patch_integral_independence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:23:15.5649+00:00
-- url     : https://prove2.me/theorems/8f396098-41fd-43c0-a1ec-5b4f1967ebb1
-- title:
--   Signed original predictable UBV generator drift integral is invariant under exact-cap boundary value patches
-- statement:
--   For genuine spectrally negative unbounded-variation Levy source X and original capped same-filtration control D, let μ be any fixed s-finite atomless physical-time clock. On one full P-probability event, every two real-valued generator/drift densities F,G (chosen after the sample path) whose values agree at all positive pre-ruin times except possibly when exact original predictable pre-event reserve leftLim(x+X−rightLimit D) equals cap c have identical ordinary real Bochner integrals over the original surviving time interval. This directly permits arbitrary cap-point generator patch definitions for the signed discounted HJB drift when the verification candidate is C² only strictly below cap, including initial x=c. The assertion is only about a fixed atomless clock and not random cap local-time or dividend Stieltjes measure.
-- source:
--   Proved original UBV μ-cap occupation cc500549-ba08-47b0-b5c0-07c7a9bb40f3; predictable/current bridge 89e50cbf-efd7-4c66-8cd6-2d1e99de1a8d. Supports corrected canonical UBV core 429e17ca-5528-40b5-b593-7c03973d0706 unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_same_source_sigma_finite_cap_occupation
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_prejump_equals_book_reserve_atomless_nnreal_clock

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_signed_generator_cap_value_patch_integral_independence
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ ω ∂P, ∀ (F G : ℝ≥0 → Ω → ℝ),
      (∀ t : ℝ≥0, 0 < t →
        (t : ℝ≥0∞) < ruinTime X x D ω →
        Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ≠ c →
        F t ω = G t ω) →
      (∫ t : ℝ≥0,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω
        then F t ω else 0 ∂μ) =
      (∫ t : ℝ≥0,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω
        then G t ω else 0 ∂μ) := by sorry
