-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a07_original_ae_random_prefix_HJB_initial_event_nonpositive
-- name    : AvramDividend.Classical.avram_a07_original_ae_random_prefix_HJB_initial_event_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:51:57.907598+00:00
-- url     : https://prove2.me/theorems/55504a79-1e4d-4502-8025-40bc4079c9ec
-- title:
--   Original random HJB prefix has nonpositive initial-event integral under ae interior localisation
-- statement:
--   Only an almost-everywhere pathwise interior hypothesis is required for nonpositivity of the actual stopped random finite-grid HJB sum on all initial-filtration events. This matches stochastic sample path localisation and does not require a global interior condition.
-- source:
--   AE-localised initial-event theorem from proved 025d789c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a07_original_ae_random_prefix_HJB_initial_event_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (u : ℕ → ℝ≥0) (hu : Monotone u)
    (k : Ω → ℕ)
    (hregion : ∀ᵐ ω ∂P, ∀ i, i < k ω →
      0 < riskProcess X x D (u i) ω ∧
      ENNReal.ofReal (riskProcess X x D (u i) ω) < C)
    (G : Ω → ℝ)
    (hG : ∀ ω, G ω =
      (∑ i ∈ Finset.range (k ω),
        Real.exp (-(q * (u i : ℝ))) *
          (((u (i + 1) : ℝ) - (u i : ℝ)) *
            (X.generator w (riskProcess X x D (u i) ω) -
              q * w (riskProcess X x D (u i) ω)) +
          (D (u (i + 1)) ω - D (u i) ω) *
            (1 - deriv w (riskProcess X x D (u i) ω)))))
    (hGI : Integrable G P) :
    ∀ (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
      (∫ ω in A, G ω ∂P) ≤ 0 := by sorry
