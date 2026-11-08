-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_turn8_exact_source_F_uniformIntegrable
-- name    : AvramDividend.Classical.avram_ubv_finite9_turn8_exact_source_F_uniformIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T21:42:52.507195+00:00
-- url     : https://prove2.me/theorems/e5f7991f-e547-4eff-8480-35a064a20e98
-- title:
--   Finite-cap true stopped source F uniformly integrable from original closed cash
-- statement:
--   For the original dividend strategy with finite cap, the source-exact family of stopped post-right-payment value plus paymentTimes closed-clock dividend cash is uniformly integrable under the actual terminal cash integrability and integrability of each stopped payoff. This composes the already proved finite-cap common envelope theorem with exact original Cash and F declarations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_full_F_family_uniformIntegrable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_finite9_turn8_exact_source_F_uniformIntegrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (hfinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hCashI : Integrable Cash P)
    (σ : ℕ → Ω → ℝ≥0)
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P) :
    UniformIntegrable F (1 : ℝ≥0∞) P := by sorry
