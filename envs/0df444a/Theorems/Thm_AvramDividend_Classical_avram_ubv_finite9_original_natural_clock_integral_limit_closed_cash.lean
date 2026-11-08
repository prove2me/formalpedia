-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_natural_clock_integral_limit_closed_cash
-- name    : AvramDividend.Classical.avram_ubv_finite9_original_natural_clock_integral_limit_closed_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:52:12.50126+00:00
-- url     : https://prove2.me/theorems/7d865b85-589a-43dd-baf3-9bb40c8a558e
-- title:
--   Natural bounded-clock expectations converge to exact terminal plus inclusive dividend cash
-- statement:
--   For the actual original post-right-payment payoff at each natural time truncation min(tau,k), prove convergence of expectations to the exactly defined discounted terminal value plus closed-clock dividend cash at tau. The Proved finite-cap uniform integrable domination theorem supplies Bochner dominated convergence. The independently published natural-clock eventually-equal source lemma proves samplewise convergence without any endpoint continuity assumption, retaining time-zero, terminal, and ruin dividend atoms.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_finite9_original_natural_clock_integral_limit_closed_cash
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
    (hFmeas : ∀ k, AEStronglyMeasurable (F k) P)
    (n : ℕ) (hBound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hσeq : ∀ k ω, σ k ω = min (τ ω) (k : ℝ≥0)) :
    Tendsto (fun k => ∫ ω, F k ω ∂P) Filter.atTop
      (𝓝 (∫ ω, Term ω + Cash ω ∂P)) := by sorry
