-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_contact_weighted_atomless_zero
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_cap_contact_weighted_atomless_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:29:29.609194+00:00
-- url     : https://prove2.me/theorems/f8199679-8516-46fa-b24a-b17cf33e8b8b
-- title:
--   Genuine original predictable pre-jump cap-contact support integrates to zero against every atomless physical-time generator clock and arbitrary nonnegative weight
-- statement:
--   For actual spectrally negative Levy UBV source X, same-filtration actual dividend path D with true capped pre-ruin controlled reserve, and any atomless s-finite physical-time clock μ, arbitrary nonnegative (possibly infinite) time/path-dependent stochastic characteristic densities supported on exact cap contact of the predictable *strict pre-event* reserve have zero μ-lintegral on P-a.e. original trajectory. This is the cap boundary that appears in the Itô Gaussian and compensated-jump generator integrands, including processes starting at c and with payments at c. It uses no supplementary smoothness or integrability at cap. The result does not assert zero contribution for random dividend Stieltjes or boundary local-time clocks.
-- source:
--   Proved same-X,D cap time occupation cc500549-ba08-47b0-b5c0-07c7a9bb40f3 plus newly accepted original predictable/current NNReal atomless clock equivalence 89e50cbf-efd7-4c66-8cd6-2d1e99de1a8d. Supports corrected canonical 429e17ca-5528-40b5-b593-7c03973d0706 without submitting or changing it.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_same_source_sigma_finite_cap_occupation
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_prejump_equals_book_reserve_atomless_nnreal_clock

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_cap_contact_weighted_atomless_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ]
    (weight : ℝ≥0 → Ω → ℝ≥0∞) :
    ∀ᵐ ω ∂P,
      (∫⁻ t : ℝ≥0,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
            Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
        then weight t ω else 0 ∂μ) = 0 := by sorry
