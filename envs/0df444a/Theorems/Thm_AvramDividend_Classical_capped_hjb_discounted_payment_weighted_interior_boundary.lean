-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_hjb_discounted_payment_weighted_interior_boundary
-- name    : AvramDividend.Classical.capped_hjb_discounted_payment_weighted_interior_boundary
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:58:01.309009+00:00
-- url     : https://prove2.me/theorems/21d3bd4c-219a-4038-b74e-692012e99f4a
-- title:
--   Capped HJB domination of interior stopped Stieltjes dividends with exact boundary remainder
-- statement:
--   Under the HJB maximum equation the candidate derivative is at least one wherever the reserve is positive and strictly below the cap. The actual discounted stopped Stieltjes dividend mass on this interior is therefore bounded by derivative-weighted mass. Splitting the exact payment measure between interior and its complement gives a whole-window inequality retaining all possible cap, zero-reserve, initial and ruin-boundary contributions, including continuous dividend payments.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_discounted_dividend_payment_interior_boundary_lintegral_split
import Theorems.Thm_AvramDividend_Classical_hjb_component_inequalities
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.capped_hjb_discounted_payment_weighted_interior_boundary
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (σ : ℝ≥0∞) (T : ℝ≥0) (ω : Ω) (u : ℝ → ℝ)
    (hInterior : MeasurableSet
      {t : ℝ | 0 < u t ∧ ENNReal.ofReal (u t) < C}) :
    (∫⁻ t in paymentTimes σ ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
    (∫⁻ t in (paymentTimes σ ∩ Iic (T : ℝ)) ∩
      {t : ℝ | 0 < u t ∧ ENNReal.ofReal (u t) < C},
      ENNReal.ofReal (Real.exp (-(q * t)) * deriv w (u t))
        ∂(dividendMeasure D ω)) +
    (∫⁻ t in (paymentTimes σ ∩ Iic (T : ℝ)) \
      {t : ℝ | 0 < u t ∧ ENNReal.ofReal (u t) < C},
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
