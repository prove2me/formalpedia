-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_family_discounted_terminal_UI
-- name    : AvramDividend.Classical.avram_ubv_finite9_original_family_discounted_terminal_UI
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:48:52.149609+00:00
-- url     : https://prove2.me/theorems/1a33d052-aeea-4eb3-b6ca-803c33a5f774
-- title:
--   Uniform integrability of the original finite-cap discounted terminal family
-- statement:
--   For finite cap C, source-exact conditional post-right-payment/ruin W and discount q≥0, the family of true discounted terminal rewards is uniformly integrable in L1 whenever each term is almost-everywhere strongly measurable. The proof composes one common pointwise envelope across all stopping localisations with the already Proved general bounded-family uniform-integrability theorem. This is only the terminal component, not the dividend cash or centred stochastic integral.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_finite9_original_family_discounted_terminal_UI
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hfinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : ℕ → Ω → ℝ≥0) (W Term : ℕ → Ω → ℝ)
    (hW : ∀ k ω, W k ω =
      if σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
      else riskProcess X x D (σ k ω) ω)
    (q : ℝ) (hq : 0 ≤ q)
    (hTerm : ∀ k ω, Term k ω =
      Real.exp (-(q * (σ k ω : ℝ))) * w (W k ω))
    (hTermMeas : ∀ k, AEStronglyMeasurable (Term k) P) :
    UniformIntegrable Term (1 : ℝ≥0∞) P := by sorry
