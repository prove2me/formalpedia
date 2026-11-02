-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_zero_uniform_all_characteristic_weights
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_cap_zero_uniform_all_characteristic_weights
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:59:53.788281+00:00
-- url     : https://prove2.me/theorems/35fd2e0a-aab2-4685-8bce-b53aa9dbdd00
-- title:
--   One original-process full-probability event annihilates cap-supported predictable generator densities for ALL nonnegative weights simultaneously
-- statement:
--   For the actual original spectrally negative UBV Lévy source and same-filtration capped control D, and a fixed atomless s-finite physical-time clock μ, there exists a P-conull event where EVERY weight function t,ω↦[0,∞], including arbitrary nonmeasurable, unbounded and infinite-at-cap densities, has zero positive pre-ruin μ-integral when restricted to exact cap contact of true original predictable leftLim(x+X−rightLimit D). The quantifiers are strengthened from ∀weight,∀ᵐω to ∀ᵐω,∀weight using source cap occupation and preevent-current pathwise chronology which are themselves independent of the weight. This is a uniform stochastic generator boundary lemma for all subsequent Gaussian/jump characteristics and localisation weights, including x=c, with no dividend interior assumption. Local time and random dividend Stieltjes clocks are not nullified.
-- source:
--   Proved original deterministic-clock cap occupation cc500549-ba08-47b0-b5c0-07c7a9bb40f3 and chronological predictable/current bridge 89e50cbf-efd7-4c66-8cd6-2d1e99de1a8d. Supports corrected canonical UBV core 429e17ca-5528-40b5-b593-7c03973d0706 untouched.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_same_source_sigma_finite_cap_occupation
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_prejump_equals_book_reserve_atomless_nnreal_clock

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_cap_zero_uniform_all_characteristic_weights
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ ω ∂P, ∀ weight : ℝ≥0 → Ω → ℝ≥0∞,
      (∫⁻ t : ℝ≥0,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
            Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
        then weight t ω else 0 ∂μ) = 0 := by sorry
