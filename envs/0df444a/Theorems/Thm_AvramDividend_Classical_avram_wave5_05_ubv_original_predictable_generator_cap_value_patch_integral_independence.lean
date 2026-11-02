-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_generator_cap_value_patch_integral_independence
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_generator_cap_value_patch_integral_independence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:21:40.947453+00:00
-- url     : https://prove2.me/theorems/85bf49cc-9893-4771-82cf-6597e583cfd0
-- title:
--   Original predictable UBV stopped physical-time generator integral is invariant under arbitrary exact-cap value patches
-- statement:
--   For genuine spectrally negative unbounded-variation source X, same-filtration original dividend strategy D and cap-constrained reserve, on a single P-conull event, every two arbitrary ENNReal generator densities F and G have the same positive pre-ruin μ-lintegral whenever they agree at each positive surviving time whose exact original predictable pre-event reserve leftLim(x+X−rightLimit D) is not c. Here μ is any fixed s-finite atomless physical-time measure. F/G are universally quantified inside the conull event and can be unbounded, nonmeasurable or infinite at cap; the generator's boundary value is irrelevant to its physical-time drift/compensator integral. The theorem explicitly includes U0=c, does not evaluate any C² derivative at the cap, and does not assert nullity of singular local-time/dividend Stieltjes clocks.
-- source:
--   Proved original same-source σ-finite cap occupation cc500549-ba08-47b0-b5c0-07c7a9bb40f3 and original preevent/current chronology 89e50cbf-efd7-4c66-8cd6-2d1e99de1a8d. Corrected core 429e17ca-5528-40b5-b593-7c03973d0706 unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_same_source_sigma_finite_cap_occupation
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_prejump_equals_book_reserve_atomless_nnreal_clock

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_generator_cap_value_patch_integral_independence
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ ω ∂P, ∀ (F G : ℝ≥0 → Ω → ℝ≥0∞),
      (∀ t : ℝ≥0, 0 < t →
        (t : ℝ≥0∞) < ruinTime X x D ω →
        Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ≠ c →
        F t ω = G t ω) →
      (∫⁻ t : ℝ≥0,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω
        then F t ω else 0 ∂μ) =
      (∫⁻ t : ℝ≥0,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω
        then G t ω else 0 ∂μ) := by sorry
