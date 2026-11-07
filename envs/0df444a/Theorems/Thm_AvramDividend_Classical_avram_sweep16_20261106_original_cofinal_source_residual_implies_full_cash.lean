-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_20261106_original_cofinal_source_residual_implies_full_cash
-- name    : AvramDividend.Classical.avram_sweep16_20261106_original_cofinal_source_residual_implies_full_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:49:25.316291+00:00
-- url     : https://prove2.me/theorems/1e7e5197-f66c-41db-ba49-6e818ccf899b
-- title:
--   Genuine original cofinal stopped Itô residual witnesses imply the complete physical ruin-horizon dividend upper budget
-- statement:
--   For the unchanged original Lévy process, the exact samplewise W/Cash/Term and L1 signed residual witnesses on every natural bounded ruin clock and every cofinal right-continuous stopping localizer imply the complete original ruin dividend cash upper bound at every real horizon. The L1 mean-zero martingale requirement and both signed drift inequalities are explicit in hResidual. The proof uses the already Proved natural-clock budget theorem 3b8e6210 for each n, then the independently reduced cash/horizon bridge ec080252.
-- source:
--   Source-exact SWEEP16 reduction for canonical 750ad13b and corrected UBV 429e17ca; imports in proof only after the exact required Proved certificates exist. This is a conditional theorem exposing the genuine stochastic Ito-Meyer gap; it does not assume an unproven local martingale has mean zero or alter the physical process. The large residual assumption is deliberately an explicit child obligation for parallel proof work.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_sweep16_20261106_original_cofinal_source_residual_implies_full_cash
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
    (T : ℝ)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSstop : ∀ k, IsStoppingTime 𝓕.rightCont (S k))
    (hSmono : ∀ ω, Monotone (fun k => S k ω))
    (hSsup : ∀ ω, (⨆ k : ℕ, S k ω) = ⊤)
    (τ : ℕ → ℕ → Ω → ℝ≥0)
    (hτeq : ∀ n k ω, τ n k ω =
      (min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal)
    (hResidual : ∀ n k : ℕ, ∃ W Cash Term M G H : Ω → ℝ,
      (∀ ω, W ω = if τ n k ω = 0 ∨
        (τ n k ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ n k ω) ω - rightLimit D (τ n k ω) ω
        else riskProcess X x D (τ n k ω) ω) ∧
      (∀ ω, Cash ω =
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ n k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) ∧
      (∀ ω, Term ω = Real.exp (-(q * (τ n k ω : ℝ))) * w (W ω)) ∧
      Integrable Term P ∧ Integrable Cash P ∧
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + G ω + H ω)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    ENNReal.ofReal (w x) := by sorry
