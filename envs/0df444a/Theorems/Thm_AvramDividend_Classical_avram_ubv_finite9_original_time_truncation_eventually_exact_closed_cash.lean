-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_time_truncation_eventually_exact_closed_cash
-- name    : AvramDividend.Classical.avram_ubv_finite9_original_time_truncation_eventually_exact_closed_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:49:07.06145+00:00
-- url     : https://prove2.me/theorems/fb7ff5e9-92da-48d1-bb1e-df1b4983591e
-- title:
--   Exact eventual identity of the original natural time-truncated F and closed-clock terminal payoff
-- statement:
--   For a bounded original stopping clock tau, the natural truncations min(tau,k) eventually equal tau on every sample path. Consequently the exact original discounted post-right-payment reward plus inclusive dividend cash through min(tau,k) eventually coincides with Term plus Cash, including time-zero, ruin, and terminal-horizon payments. This is an exact identity without continuity or a finite-cap limiting argument; it uses the previously Proved original stopping-clock truncation lemma.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_finite9_original_time_truncation_eventually_exact_closed_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (n : ℕ)
    (hBound : ∀ ω, τ ω ≤ (n : ℝ≥0))
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
    (σ : ℕ → Ω → ℝ≥0)
    (hσeq : ∀ k ω, σ k ω = min (τ ω) (k : ℝ≥0))
    (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) :
    ∀ ω, ∀ᶠ k : ℕ in Filter.atTop, F k ω = Term ω + Cash ω := by sorry
