-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_atomless_predictable_infinite_cap_generator_HJB_ae
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_atomless_predictable_infinite_cap_generator_HJB_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:33:25.555324+00:00
-- url     : https://prove2.me/theorems/70cbcd95-c66a-4c1c-9114-fd61e2f957e4
-- title:
--   True original predictable stopped infinite-cap pre-event reserve has generator integrability and HJB sign a.e.
-- statement:
--   When source admissibility cap is infinity, the zero boundary is the only physical-time HJB endpoint. On any deterministic s-finite atomless original time measure and before any ruin-dominated random clock, source zero occupation plus genuine pre-event/book reserve a.e equality transfer both Levy GeneratorIntegrable and generator-minus-q nonpositive to the actual predictable left-limit reserve. Positive times are essential for the left-limit identity.
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

theorem AvramDividend.Classical.avram_p4_e_localise_original_atomless_predictable_infinite_cap_generator_HJB_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x ⊤ D)
    (hDiv : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0∞)
    (hτ : ∀ ω, τ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ]
    (w : ℝ → ℝ) (q : ℝ)
    (hwGen : ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) :
    ∀ᵐ ω ∂P, ∀ᵐ t : ℝ≥0 ∂μ,
      0 < t → (t : ℝ≥0∞) < τ ω →
      X.GeneratorIntegrable w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ∧
        X.generator w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) - q * w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ≤ 0 := by sorry
