-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_hjb_actual_dividend_le_derivative_weighted
-- name    : AvramDividend.Classical.capped_hjb_actual_dividend_le_derivative_weighted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:31:42.276991+00:00
-- url     : https://prove2.me/theorems/7589ee69-00e5-40b6-b108-5a9a30b70d52
-- title:
--   HJB gradient bounds actual stopped Stieltjes payments by derivative-weighted payments
-- statement:
--   On any actual stopped dividend payment window lying in the strictly positive reserve interior below a cap, the HJB maximum equation forces the candidate derivative to be at least one. Therefore the actual discounted real Stieltjes payout is at most the derivative-weighted payout, provided that the latter is integrable.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_discounted_actual_dividend_le_derivative_weighted
import Theorems.Thm_AvramDividend_Classical_hjb_component_inequalities

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.capped_hjb_actual_dividend_le_derivative_weighted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (σ : ℝ≥0∞) (T : ℝ≥0) (ω : Ω) (u : ℝ → ℝ)
    (hregion : ∀ t ∈ paymentTimes σ ∩ Iic (T : ℝ),
      0 < u t ∧ ENNReal.ofReal (u t) < C)
    (hWeighted : IntegrableOn (fun t : ℝ =>
      Real.exp (-(q * t)) * deriv w (u t))
      (paymentTimes σ ∩ Iic (T : ℝ)) (dividendMeasure D ω)) :
    (∫ t in paymentTimes σ ∩ Iic (T : ℝ),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ≤
    (∫ t in paymentTimes σ ∩ Iic (T : ℝ),
      Real.exp (-(q * t)) * deriv w (u t) ∂(dividendMeasure D ω)) := by sorry
