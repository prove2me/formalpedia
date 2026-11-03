-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_09_corrected_positive_cap_bv_parent_no_explicit_preruin_value_hypothesis
-- name    : AvramDividend.Classical.avram_wave7_09_corrected_positive_cap_bv_parent_no_explicit_preruin_value_hypothesis
-- status  : Open
-- author  : @WillR
-- created : 2026-11-02T18:31:25.888701+00:00
-- url     : https://prove2.me/theorems/7ec2ce81-ae92-463a-9ade-45c2abd2007d
-- title:
--   Corrected BV parent with pre-ruin candidate nonnegativity made a derived lemma rather than an extra hypothesis
-- statement:
--   Under exactly the original corrected positive-cap BV parent's Standing, BV, discount, candidate regularity, nonnegative w(0), HJB generator/gradient, capped admissibility and nonnegative horizon hypotheses, its pre-ruin candidate sign condition hw_nonneg is mathematically redundant. Proved helper 151fa4ac derives it from original capped pre-ruin reserve range and the full-cap gradient secant. This stronger corrected BV value bound reduces to the exact corrected positive-cap parent 8c16239e, without changing or submitting its exclusively owned ef7e6c20 stochastic core. As the parent 8c16239e remains Open, this theorem must be reported only as an accepted sketch until that dependency becomes Proved.
-- source:
--   Proved positive-cap BV automatic pre-ruin sign 151fa4ac and genuinely Open corrected parent 8c16239e; same canonical Ω/P/𝓕/X, ruinTime, paymentTimes, dividendMeasure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_09_corrected_positive_cap_bv_parent_no_explicit_preruin_value_hypothesis
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
