-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_turn8_original_F_vanishing_localisation_events_L1
-- name    : AvramDividend.Classical.avram_ubv_finite9_turn8_original_F_vanishing_localisation_events_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T22:03:46.62281+00:00
-- url     : https://prove2.me/theorems/9af17333-177e-4a9d-8e0b-c521255a1336
-- title:
--   Source-exact finite-cap stopped payoff vanishes in L1 on negligible localisation events
-- statement:
--   Under finite cap and integrable actual closed-clock Cash and all original stopped F(k), for any sequence of measurable localisation events with probabilities converging to zero, the L1 norms of the exact stopped discounted post-right-payment value plus dividend cash restricted to those events tend to zero. This derives a genuinely sequential localisation estimate from the previously proved source-exact UI theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_turn8_exact_source_F_uniformIntegrable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_finite9_turn8_original_F_vanishing_localisation_events_L1
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
    (hFI : ∀ k, Integrable (F k) P)
    (A : ℕ → Set Ω) (hA : ∀ k, MeasurableSet (A k))
    (hPA : Tendsto (fun k => P (A k)) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm ((A k).indicator (F k)) (1 : ℝ≥0∞) P)
      atTop (𝓝 0) := by sorry
