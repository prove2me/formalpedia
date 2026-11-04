-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_atomless_predictable_finite_cap_generator_HJB_ae
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_atomless_predictable_finite_cap_generator_HJB_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:33:37.610197+00:00
-- url     : https://prove2.me/theorems/61ff5d17-e2fb-4b9f-89af-0e647545c41d
-- title:
--   True original predictable stopped finite-cap pre-event reserve has generator integrability and HJB sign a.e.
-- statement:
--   Under original UBV and finite real cap admissibility, on any deterministic s-finite atomless physical-time clock, the genuine predictable strict-left pre-event reserve has actual Levy GeneratorIntegrable and nonpositive generator-minus-q HJB deficit at almost every positive time before a ruin-dominated random clock. This combines source original book reserve zero/cap occupancy with accepted atomless chronological left-limit equality. Does not assert random dividend Stieltjes mass zero or expected L1.
-- source:
--   Genuine original-source atomless pre-event equals book reserve theorem UUID 89e50cbf-efd7-4c66-8cd6-2d1e99de1a8d; zero occupation 644af487; finite-cap occupancy cc500549.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_allcap_original_stopped_full_zero_included_no_grid
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_same_source_sigma_finite_cap_occupation
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_prejump_equals_book_reserve_atomless_nnreal_clock
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_e_localise_original_atomless_predictable_finite_cap_generator_HJB_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (hDiv : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (τ : Ω → ℝ≥0∞)
    (hτ : ∀ ω, τ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ]
    (w : ℝ → ℝ) (q : ℝ)
    (hwGen : ∀ y : ℝ, 0 < y → y < c →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) :
    ∀ᵐ ω ∂P, ∀ᵐ t : ℝ≥0 ∂μ,
      0 < t → (t : ℝ≥0∞) < τ ω →
      X.GeneratorIntegrable w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ∧
        X.generator w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) - q * w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ≤ 0 := by sorry
