-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_turn8_original_F_small_event_L1_control
-- name    : AvramDividend.Classical.avram_ubv_finite9_turn8_original_F_small_event_L1_control
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T21:58:21.478944+00:00
-- url     : https://prove2.me/theorems/6a29c47e-bfda-4ed2-889c-207e55d9a5e0
-- title:
--   Source-exact stopped dividend payoff has uniformly small L1 mass on small events
-- statement:
--   For the original finite-cap controlled Lévy reserve, the exact stopped post-right-payment value plus closed-clock dividend cash has uniformly small L1 norm on sufficiently small measurable events, uniformly over all stopped clocks. This is the small-event localisation consequence of the proven source-exact uniform-integrability bound and preserves the actual F and Cash definitions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_turn8_exact_source_F_uniformIntegrable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_finite9_turn8_original_F_small_event_L1_control
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
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (k : ℕ) (s : Set Ω), MeasurableSet s →
        P s ≤ ENNReal.ofReal δ →
        eLpNorm (s.indicator (F k)) (1 : ℝ≥0∞) P ≤ ENNReal.ofReal ε := by sorry
