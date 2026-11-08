-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_full_F_family_uniformIntegrable
-- name    : AvramDividend.Classical.avram_ubv_finite9_original_full_F_family_uniformIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:44:48.420962+00:00
-- url     : https://prove2.me/theorems/2c6c3550-2a35-42df-8f6e-1377b7667a01
-- title:
--   Uniform integrability of the full original finite-cap stopped terminal-plus-cash payoff family
-- statement:
--   The true original finite-cap localisation family F includes discounted post-right-payment terminal value and all dividend cash through the closed clock. Its uniform terminal bound and the assumed integrability of the full terminal-clock cash yield a single integrable envelope independent of k. The generic integrable-domination theorem then proves UniformIntegrable F in L1, preserving the exact original process, stopping times, ruin and endpoint payment atoms.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_finite9_original_full_F_family_uniformIntegrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (hfinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0)
    (hCashτI : Integrable
      (fun ω => (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) P)
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
    (hFmeas : ∀ k, AEStronglyMeasurable (F k) P) :
    UniformIntegrable F (1 : ℝ≥0∞) P := by sorry
