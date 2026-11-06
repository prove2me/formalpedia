-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_cofinal_ito_budget_to_signed_witness
-- name    : AvramDividend.Classical.avram_p4_f3_original_cofinal_ito_budget_to_signed_witness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T22:54:51.345455+00:00
-- url     : https://prove2.me/theorems/11e76b96-8581-4bd9-9066-0d7866c0fb5d
-- title:
--   Original cofinal stopped physical Ito budgets directly imply three signed UBV source witnesses
-- statement:
--   For the same original X,D, true natural ruin clock and cofinal localising clocks, if all original discounted terminal-plus-full closed Stieltjes cash rewards are integrable with expected budget bounded by w(x), then the exact natural-clock three-witness signed Ito residual inequality holds. This composes the Proved F4 physical cofinal Fatou/five-witness route with the Proved F3 nonintegrable-residual elimination. No import of the Open fdb9a6a3 or canonical 0dda1be7 is used; the local Itô expectation budget remains an explicit future source obligation.
-- source:
--   Independent Proved F4 cofinal physical stopped expectation-to-five-witness theorem 08c01de9, composed with F3 Proved ac622130. It isolates the genuinely missing local expected Ito budget without imposing natural-clock martingale UI.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_f3_original_cofinal_ito_budget_to_signed_witness
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
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
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (hWk : ∀ k ω, Wk k ω =
      if τk k ω = 0 ∨ (τk k ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τk k ω) ω - rightLimit D (τk k ω) ω
      else riskProcess X x D (τk k ω) ω)
    (hCashk : ∀ k ω, Cashk k ω =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τk k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)
    (hTermk : ∀ k ω, Termk k ω =
      Real.exp (-(q * (τk k ω : ℝ))) * w (Wk k ω))
    (hFmeas : ∀ k, Measurable (fun ω => Termk k ω + Cashk k ω))
    (hFint : ∀ k, Integrable (fun ω => Termk k ω + Cashk k ω) P)
    (hBudget : ∀ k, (∫ ω, Termk k ω + Cashk k ω ∂P) ≤ w x) :
    ∃ M G H : Ω → ℝ,
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + G ω + H ω) := by sorry
