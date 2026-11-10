-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin18_original_bounded_clock_cofinal_full_reward_eventually_exact
-- name    : AvramDividend.Classical.avram_mix_fin18_original_bounded_clock_cofinal_full_reward_eventually_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T01:17:48.795829+00:00
-- url     : https://prove2.me/theorems/5e436f12-c5bd-4cb8-8fc4-612d5badbbf3
-- title:
--   Cofinal spatial stops preserve the exact original arbitrary bounded-clock reward and terminal cash
-- statement:
--   For any source-original finite-time stopped clock sigma bounded by n, an increasing spatial cutoff whose supremum is infinity almost surely eventually exceeds sigma. Hence min(sigma,cutoff) equals sigma on each sample path beyond a finite index, and the entire discounted postpayment terminal value plus closed inclusive-horizon Stieltjes dividend cash agrees exactly, including zero, ruin and final-horizon atoms. This extends the proved natural-ruin-clock cofinality theorem to arbitrary bounded stopping clocks, as required by the mixed finite Ito localisation. No expectation or large-jump moment assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin18_original_bounded_clock_cofinal_full_reward_eventually_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (σ : Ω → ℝ≥0)
    (hσbound : ∀ ω, (σ ω : ℝ≥0∞) ≤ (n : ℝ≥0∞))
    (S : ℕ → Ω → ℝ≥0∞)
    (hSmono : ∀ ω, Monotone (fun k => S k ω))
    (hSsup : ∀ᵐ ω ∂P, (⨆ k : ℕ, S k ω) = ⊤)
    (σk : ℕ → Ω → ℝ≥0)
    (hσk : ∀ k ω, σk k ω = (min (σ ω : ℝ≥0∞) (S k ω)).toNNReal)
    (F : Ω → ℝ) (Fk : ℕ → Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨
              (σ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ ω) ω - rightLimit D (σ ω) ω
          else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFksource : ∀ k ω, Fk k ω =
      Real.exp (-(q * (σk k ω : ℝ))) *
        w (if σk k ω = 0 ∨
              (σk k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σk k ω) ω - rightLimit D (σk k ω) ω
          else riskProcess X x D (σk k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σk k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) :
    ∀ᵐ ω ∂P, ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      σk k ω = σ ω ∧ Fk k ω = F ω := by sorry
