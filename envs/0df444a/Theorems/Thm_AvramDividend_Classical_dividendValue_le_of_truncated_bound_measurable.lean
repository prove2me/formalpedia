-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendValue_le_of_truncated_bound_measurable
-- name    : AvramDividend.Classical.dividendValue_le_of_truncated_bound_measurable
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T09:35:11.908685+00:00
-- url     : https://prove2.me/theorems/70aeb705-1f56-4a8d-a202-c5f1f77d0719
-- title:
--   Truncated expected dividend bounds imply the full dividend-value bound when the truncated payoff is measurable
-- statement:
--   If all truncated discounted dividend expectations are bounded by M and their pathwise truncated payout functionals are measurable in ω, then the full dividendValue is bounded by M. Pointwise, the full discounted Stieltjes integral equals the supremum over finite horizons, including continuous dividends. The outer nonnegative Lebesgue integral therefore commutes with the increasing supremum by monotone convergence, yielding the bound. This isolates random truncated-payout measurability as the last technical precondition when converting the open BV/UBV stochastic leaves to the full value-function estimate.
-- source:
--   Child discounted_dividend_integral_iSup_truncated and pinned Mathlib lintegral_iSup, lintegral_mono_set.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendValue_le_of_truncated_bound_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (D : ℝ≥0 → Ω → ℝ) (M : ℝ≥0∞)
    (hMeas : ∀ n : ℕ, Measurable (fun ω : Ω =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)))
    (hBound : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ M) :
    dividendValue X q x D ≤ M := by sorry
