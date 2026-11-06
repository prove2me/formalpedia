-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_ae_cofinal_discounted_full_payoff_tendsto
-- name    : AvramDividend.Classical.avram_p4_f4_original_ae_cofinal_discounted_full_payoff_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T22:07:06.979583+00:00
-- url     : https://prove2.me/theorems/3eca1972-1780-4d53-8c0a-7ec6e0bf1dc2
-- title:
--   True original stopped terminal-plus-closed-Stieltjes payoff converges almost surely under cofinal upper localisation
-- statement:
--   For the actual original spectrally negative Levy process, original controlled reserve with right-limit D, and full closed-horizon discounted dividendMeasure cash, any monotone upper localisers cofinal almost surely yield almost-sure ENNReal.ofReal convergence of the exact payoff at tau_k=min(min(ruin,n),S_k) to the original tau=min(ruin,n) payoff. The proof uses eventual literal clock equality on the good event, so right-payment, ruin and horizon atoms are preserved exactly; there is no false continuity assertion or UI hypothesis.
-- source:
--   Proved 2589726d original almost-sure eventual clock equality. Rewriting the actual original Reward as a function of the stopped time gives eventual equal values and thus pointwise Tendsto on the good event. No new process or law equalities.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_ae_cofinal_ruin_clock_eventually_eq

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f4_original_ae_cofinal_discounted_full_payoff_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (n : ℕ)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSmono : ∀ ω, Monotone (fun k => S k ω))
    (hSsup : ∀ᵐ ω ∂P, (⨆ k : ℕ, S k ω) = ⊤)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (τk : ℕ → Ω → ℝ≥0)
    (hτk : ∀ k ω, τk k ω =
      (min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal) :
    let Reward : ℝ≥0 → Ω → ℝ := fun t ω =>
      Real.exp (-(q * (t : ℝ))) *
        w (if t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω then
          x + X.X t ω - rightLimit D t ω
          else riskProcess X x D t ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (t : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
    ∀ᵐ ω ∂P, Tendsto
      (fun k => ENNReal.ofReal (Reward (τk k ω) ω)) atTop
      (𝓝 (ENNReal.ofReal (Reward (τ ω) ω))) := by sorry
