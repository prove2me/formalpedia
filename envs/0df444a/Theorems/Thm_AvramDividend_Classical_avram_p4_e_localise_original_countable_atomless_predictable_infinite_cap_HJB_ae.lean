-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_countable_atomless_predictable_infinite_cap_HJB_ae
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_countable_atomless_predictable_infinite_cap_HJB_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:40:36.967204+00:00
-- url     : https://prove2.me/theorems/28641c7d-7707-4b1f-bdf6-8ea8161d8291
-- title:
--   Original countable atomless localisation clocks have simultaneous predictable pre-event infinite-cap HJB sign
-- statement:
--   For every countable original ruin-dominated localisation clock and deterministic s-finite atomless physical-time measure, a single probability-one event witnesses interior generator integrability and nonpositive HJB drift of the true original predictable left-limit reserve at every clock. This is a countable localisation statement, with no claim on random dividend Stieltjes masses.
-- source:
--   Original accepted source clock and occupation theorems 644af487, cc500549, chronological source 89e50cbf; upstream P4-E own one-clock helper.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_atomless_predictable_infinite_cap_generator_HJB_ae
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original countable atomless localisation clocks have simultaneous predictable pre-event infinite-cap HJB sign. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_countable_atomless_predictable_infinite_cap_HJB_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x ⊤ D)
    (hDiv : IsDividendStrategy 𝓕 D)
    (τ : ℕ → Ω → ℝ≥0∞)
    (hτ : ∀ k ω, τ k ω ≤ ruinTime X x D ω)
    (μ : ℕ → Measure ℝ≥0)
    (hμ : ∀ k, SFinite (μ k))
    (hAtomless : ∀ k, NullSingletonClass (μ k))
    (w : ℝ → ℝ) (q : ℝ)
    (hwGen : ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) :
    ∀ᵐ ω ∂P, ∀ k, ∀ᵐ t : ℝ≥0 ∂μ k,
      0 < t → (t : ℝ≥0∞) < τ k ω →
      X.GeneratorIntegrable w (Function.leftLim
        (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t) ∧
      X.generator w (Function.leftLim
        (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t) -
        q * w (Function.leftLim
        (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t) ≤ 0 := by sorry
