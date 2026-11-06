-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_mean_vanishing_random_error_strict_real_perpetual
-- name    : AvramDividend.Classical.avram_limit2_mean_vanishing_random_error_strict_real_perpetual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:45:41.926815+00:00
-- url     : https://prove2.me/theorems/936d66d4-f0d8-4747-bcd6-70393dc1ca99
-- title:
--   Mean-vanishing original random localisation errors yield strict perpetual real Stieltjes value bounds
-- statement:
--   An original Levy dividend strategy has a nonnegative measurable random error for every integer strict horizon, whose outer ENNReal expected error goes to zero. The discounted genuine Stieltjes cash on paymentTimes(ruinTime) plus arbitrary nonnegative terminal is bounded by finite B plus expected random error. Taking numeric error_n to be that outer lintegral gives the already Proved strict vanishing-error bridge, yielding full perpetual dividendValue ≤ B, integrable original signed real payout and exact ENNReal expected real cash identity. No fabricated martingale, terminal vanishing, equality-in-law or axioms.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_vanishing_remainder_strict_cash_real_perpetual

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_mean_vanishing_random_error_strict_real_perpetual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (B : ℝ≥0∞) (hB : B < ⊤)
    (error : ℕ → Ω → ℝ≥0∞)
    (hError : ∀ ε : ℝ≥0, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (∫⁻ ω, error n ω ∂P) ≤ (ε : ℝ≥0∞))
    (hBudget : ∀ n : ℕ, ∃ Terminal : Ω → ℝ≥0∞,
      (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iio (((n + 1 : ℕ) : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal ω) ∂P) ≤
      B + (∫⁻ ω, error n ω ∂P)) :
    dividendValue X q x D ≤ B ∧
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    dividendValue X q x D =
      ENNReal.ofReal (∫ ω,
        (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
