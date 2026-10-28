-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_dividend_payment_interior_boundary_lintegral_split
-- name    : AvramDividend.Classical.discounted_dividend_payment_interior_boundary_lintegral_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:37:43.306037+00:00
-- url     : https://prove2.me/theorems/69792ac5-6e9d-4783-9562-11a0d30604f6
-- title:
--   Split actual stopped dividend Stieltjes payout into HJB interior and boundary contributions
-- statement:
--   Every nonnegative stopped dividend Stieltjes payout splits exactly into its contribution at strictly positive below-cap reserve times and the remaining zero-reserve or cap-boundary times. The interior and boundary parts form a disjoint measurable partition of the genuine payment window. This is a localisation interface for applying the HJB inequalities only where their hypotheses hold.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.discounted_dividend_payment_interior_boundary_lintegral_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : ℝ≥0∞) (T : ℝ≥0) (ω : Ω)
    (C : ℝ≥0∞) (u : ℝ → ℝ)
    (hInterior : MeasurableSet {t : ℝ | 0 < u t ∧ ENNReal.ofReal (u t) < C})
    (f : ℝ → ℝ≥0∞) :
    (∫⁻ t in paymentTimes σ ∩ Iic (T : ℝ), f t ∂(dividendMeasure D ω)) =
      (∫⁻ t in (paymentTimes σ ∩ Iic (T : ℝ)) ∩ {t : ℝ | 0 < u t ∧ ENNReal.ofReal (u t) < C},
        f t ∂(dividendMeasure D ω)) +
      (∫⁻ t in (paymentTimes σ ∩ Iic (T : ℝ)) \ {t : ℝ | 0 < u t ∧ ENNReal.ofReal (u t) < C},
        f t ∂(dividendMeasure D ω)) := by sorry
