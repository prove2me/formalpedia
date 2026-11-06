-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_localized_ito_no_ui_ruin_cash
-- name    : AvramDividend.Classical.avram_sweep16_original_localized_ito_no_ui_ruin_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:33:41.75585+00:00
-- url     : https://prove2.me/theorems/3b8e6210-b172-4ba6-aaf0-143cbe5ea633
-- title:
--   Original localized stopped Ito residuals yield true bounded natural-ruin Stieltjes cash budget by no-UI Fatou
-- statement:
--   Under the unchanged physical X,P,D,filtration, candidate HJB sign and an increasing exhausting original stopping-localizer sequence, assume only the genuine per-clock integrable and mean-zero source Ito residual witnesses, which remain the stochastic mathematical obligation. Derive all local clock NNReal finite bounds, ruin domination and stopping-time properties from independently Proved source-exact clock theorems. Each original signed residual yields the full closed-clock expected Stieltjes cash budget; true pathwise eventually exact cash and measurable Fatou transfer yield the full bounded natural-ruin expected cash bound, with no global UI or replacement process.
-- source:
--   SWEEP16 source exact stopped-clock chain fd7f8c61, a056bf2c, f0418428, ec9db9cc, aceb77c2, ca5bbe86 and successor NNReal stopping/bound helpers.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_natural_ruin_cofinal_local_budget_to_cash
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_localized_ito_witnesses_budget_each_clock
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_double_min_clock_literal_extended_bounds
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_double_min_toNNReal_clock_rightcont_stopping
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_double_min_clock_nnreal_le_n
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_sweep16_original_localized_ito_no_ui_ruin_cash
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
    (hSstop : ∀ k, IsStoppingTime 𝓕.rightCont (S k))
    (hSmono : ∀ ω, Monotone (fun k => S k ω))
    (hSsup : ∀ ω, (⨆ k : ℕ, S k ω) = ⊤)
    (τ : ℕ → Ω → ℝ≥0)
    (hτeq : ∀ k ω, τ k ω =
      (min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal)
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
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
      Iic (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ)),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    ENNReal.ofReal (w x) := by sorry
