-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_cofinal_clock_payoff_eventually_exact
-- name    : AvramDividend.Classical.avram_p4_f4_original_cofinal_clock_payoff_eventually_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T20:15:39.329214+00:00
-- url     : https://prove2.me/theorems/4e8d0068-3930-4669-9564-d365fcece930
-- title:
--   Original bounded ruin-clock W, closed Stieltjes Cash and Term eventually equal cofinal localised versions
-- statement:
--   For the same original spectrally negative Lévy path X and admissible dividend process D, any nondecreasing cofinal localisation S_k tending to the top has S_k>n eventually, whence the original natural stopped clock min(ruin,n) equals its spatially localised min(min(ruin,n),S_k). Consequently the exact right-limit reserve, ruin branch, closed dividendMeasure cash integral including time-zero and horizon atoms, and discounted terminal payoff become literally identical pathwise. No martingale uniform integrability is claimed.
-- source:
--   Original physical stopped clock and exact payoff stabilisation, extending the accepted proof of fd7f8c61 to the reserve/terminal expression. The core cofinal clock argument is lt_iSup_iff and monotonicity, and all expressions use X, D, ruinTime, rightLimit, paymentTimes, dividendMeasure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_f4_original_cofinal_clock_payoff_eventually_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (n : ℕ)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSmono : ∀ ω, Monotone (fun k => S k ω))
    (hSsup : ∀ ω, (⨆ k : ℕ, S k ω) = ⊤)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (τk : ℕ → Ω → ℝ≥0)
    (hτk : ∀ k ω, τk k ω =
      (min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal)
    (W Cash Term : Ω → ℝ)
    (Wk Cashk Termk : ℕ → Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)
    (w : ℝ → ℝ)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hWk : ∀ k ω, Wk k ω =
      if τk k ω = 0 ∨ (τk k ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τk k ω) ω - rightLimit D (τk k ω) ω
      else riskProcess X x D (τk k ω) ω)
    (hCashk : ∀ k ω, Cashk k ω =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τk k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)
    (hTermk : ∀ k ω, Termk k ω =
      Real.exp (-(q * (τk k ω : ℝ))) * w (Wk k ω)) :
    ∀ ω, ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      τk k ω = τ ω ∧ Wk k ω = W ω ∧
      Cashk k ω = Cash ω ∧ Termk k ω = Term ω := by sorry
