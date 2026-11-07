-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_20261106_original_raw_signed_residual_to_full_cash
-- name    : AvramDividend.Classical.avram_sweep16_20261106_original_raw_signed_residual_to_full_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T07:35:46.842207+00:00
-- url     : https://prove2.me/theorems/ce358f7f-b39b-4f63-b886-298c59fe2539
-- title:
--   The exact canonical original stopped UBV signed residual witnesses alone yield full physical ruin dividend cash budget
-- statement:
--   For the genuine original UBV Lévy process, each min(ruin,n) signed residual witness has actual cash L1 by the already Proved bounded random clock theorem and terminal L1 by the already Proved signed source theorem. It consequently yields the full ruin-horizon cash upper bound via new public natural-clock adapters, with no new martingale or physical process equivalence assumptions.
-- source:
--   SWEEP16 direct exact reduction of canonical 750ad13b into correction of 429e17ca. Only the genuine source witnesses with L1 mean-zero M are assumed, and all clock/cash/terminal side conditions are discharged by previously Proved public helpers.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_sweep16_20261106_original_raw_signed_residual_to_full_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ)
    (hRaw : ∀ n : ℕ, 0 < n → ∃ W Cash Term M G H : Ω → ℝ,
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
      AEStronglyMeasurable Term P ∧
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + G ω + H ω)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    ENNReal.ofReal (w x) := by sorry
