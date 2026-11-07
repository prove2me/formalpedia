-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_20261106_original_nonnegative_signed_source_to_full_cash
-- name    : AvramDividend.Classical.avram_sweep16_20261106_original_nonnegative_signed_source_to_full_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T07:32:44.627102+00:00
-- url     : https://prove2.me/theorems/f4fe88c2-1992-45a8-8e5e-04798530d788
-- title:
--   Original nonnegative signed stopped source witnesses suffice for complete physical dividend cash without separate terminal/cash L1 assumptions
-- statement:
--   The canonical original W/Cash/Term/M/G/H source with exact natural clipped clocks, measurable nonnegative terminal and cash and true signed martingale/drift witness yields the entire ruin dividend upper budget. The full integrability of terminal and cash is derived, not assumed, using the Proved signed-domination lemma ea0155a7. Actual clock stopping comes from Proved c2b88870 and full-horizon passage from Proved 115e98d6.
-- source:
--   SWEEP16 exact decomposition of original stopped residual 750ad13b into finite-mean stochastic martingale source plus established boundary, cash-measurability and sign certificates.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_sweep16_20261106_original_nonnegative_signed_source_to_full_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
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
    (hSource : ∀ n : ℕ, 0 < n → ∃ W Cash Term M G H : Ω → ℝ,
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
      AEStronglyMeasurable Term P ∧ AEStronglyMeasurable Cash P ∧
      (∀ᵐ ω ∂P, 0 ≤ Term ω) ∧ (∀ᵐ ω ∂P, 0 ≤ Cash ω) ∧
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + G ω + H ω)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    ENNReal.ofReal (w x) := by sorry
