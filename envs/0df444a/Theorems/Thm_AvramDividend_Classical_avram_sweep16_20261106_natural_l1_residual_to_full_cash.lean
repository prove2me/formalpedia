-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_20261106_natural_l1_residual_to_full_cash
-- name    : AvramDividend.Classical.avram_sweep16_20261106_natural_l1_residual_to_full_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T07:10:04.227378+00:00
-- url     : https://prove2.me/theorems/115e98d6-9624-4193-8be5-19114cf460d1
-- title:
--   Authentic L1 stopped Ito residuals on natural bounded ruin clocks imply the entire original dividend upper budget
-- statement:
--   For the unchanged original Lévy law and right-continuous filtration, if every natural clipped ruin clock is a bounded stopping time and carries genuine integrable W/Cash/Term/M/G/H signed residual witnesses with mean-zero M and nonpositive G+H, then the entire original physical dividend upper budget holds on every real horizon. This isolates the exact L1 and stopping source obligations.
-- source:
--   SWEEP16 source-exact parallel reduction of the canonical 750ad13b original stopped residual, 429e17ca corrected UBV core and cc518136 truncated value. No local martingale is promoted to mean-zero without integrability.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_sweep16_20261106_natural_l1_residual_to_full_cash
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
    (hClock : ∀ n : ℕ, 0 < n →
      (∀ ω, (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal ≤ (n : ℝ≥0)) ∧
      IsStoppingTime 𝓕.rightCont
        (fun ω => ((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : WithTop ℝ≥0)) ∧
      (∀ ω, (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞) ≤
        ruinTime X x D ω))
    (hResidual : ∀ n : ℕ, 0 < n → ∃ W Cash Term M G H : Ω → ℝ,
      (∀ ω, W ω = if (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal = 0 ∨
        (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞) <
          ruinTime X x D ω then
        x + X.X (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal ω -
          rightLimit D (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal ω
        else riskProcess X x D (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal ω) ∧
      (∀ ω, Cash ω =
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
            Iic (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) ∧
      (∀ ω, Term ω =
        Real.exp (-(q * (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ))) *
          w (W ω)) ∧
      Integrable Term P ∧ Integrable Cash P ∧
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + G ω + H ω)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    ENNReal.ofReal (w x) := by sorry
