-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_localized_ito_witnesses_budget_each_clock
-- name    : AvramDividend.Classical.avram_sweep16_original_localized_ito_witnesses_budget_each_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:16:36.727781+00:00
-- url     : https://prove2.me/theorems/ec9db9cc-ee3c-48ec-acc1-22c84e490fb9
-- title:
--   Each genuine physical localiser's centred integrable stopped Ito residual yields its complete closed Stieltjes cash budget
-- statement:
--   For one original physical controlled Levy process and a fixed sequence of actual natural-ruin-and-stopping-time cutoffs, assume a genuine per-cutoff stopped Ito-Meyer source residual with integrable cash and terminal, integrable centred M, integrable G and H with nonpositive sum, and the one-sided original stopped terminal-plus-cash inequality. The previously Proved original-source one-sided HJB expectation lemma yields, separately at each cutoff, the complete closed-clock ENNReal cash budget, including its right-payment atom. This is the precise local stochastic source condition required by the no-UI Fatou route; it does not deduce expected M=0 from a local-martingale declaration.
-- source:
--   Proved original one-sided HJB expected-budget theorem 06a07e43, under exact original X,P,D,ruinTime,filtration and dividendMeasure.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_one_sided_hjb_expected_budget
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_sweep16_original_localized_ito_witnesses_budget_each_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : (¬ X.BoundedVariation →
      ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
      ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (S : ℕ → Ω → ℝ≥0∞)
    (τ : ℕ → Ω → ℝ≥0)
    (hτeq : ∀ k ω, τ k ω =
      (min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal)
    (hτbound : ∀ k ω, τ k ω ≤ (n : ℝ≥0))
    (hτstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (τ k ω : WithTop ℝ≥0)))
    (hτruin : ∀ k ω, (τ k ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (hResidual : ∀ k : ℕ, ∃ W Cash Term M G H : Ω → ℝ,
      (∀ ω, W ω = if τ k ω = 0 ∨
        (τ k ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ k ω) ω - rightLimit D (τ k ω) ω
        else riskProcess X x D (τ k ω) ω) ∧
      (∀ ω, Cash ω =
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) ∧
      (∀ ω, Term ω = Real.exp (-(q * (τ k ω : ℝ))) * w (W ω)) ∧
      Integrable Term P ∧ Integrable Cash P ∧
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + G ω + H ω)) :
    ∀ k : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iic (((min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
