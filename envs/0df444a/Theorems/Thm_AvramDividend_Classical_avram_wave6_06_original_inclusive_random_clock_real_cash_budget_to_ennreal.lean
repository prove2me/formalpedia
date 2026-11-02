-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_inclusive_random_clock_real_cash_budget_to_ennreal
-- name    : AvramDividend.Classical.avram_wave6_06_original_inclusive_random_clock_real_cash_budget_to_ennreal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:12:58.55664+00:00
-- url     : https://prove2.me/theorems/89e68a17-9cec-4b3e-b6b2-519a9787561c
-- title:
--   Closed random-clock original dividend cash real expectation budget implies exact ENNReal source budget
-- statement:
--   For the exact original Lévy dividendMeasure and ruin-stopped paymentTimes restricted to the CLOSED random upper clock Iic τ, show that a real cash expectation budget implies the full nested ENNReal expected discounted dividend bound. Retain the right-payment atom at τ, all continuous and singular Stieltjes mass and the zero-time atom. Assume the exact real .toReal source-cash equality and a.e. finiteness of the actual inner ENNReal payout, plus cash L1. Use ENNReal.ofReal_toReal, ofReal_integral_eq_lintegral_ofReal and lintegral_congr_ae to identify real and extended-nonnegative expectations, then monotonicity of ENNReal.ofReal. This is the exact endpoint variant missing from previously Proved source transfer 92ec1f68, whose paymentTimes(min ruin S) excludes the payment at the random stop.
-- source:
--   Source-faithful Chat 06 final expected discounted dividend output bridge; exact closed random-clock endpoint atom in Iic τ, unlike proved 92ec1f68 which uses a stopped paymentTimes set. This is deterministic measure/integrability alignment after the true same-source stopped Ito expectation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_06_original_inclusive_random_clock_real_cash_budget_to_ennreal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (τ : Ω → ℝ≥0)
    (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hCashFinite : ∀ᵐ ω ∂P,
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) < ⊤)
    (hCashI : Integrable Cash P)
    (B : ℝ) (hBudget : (∫ ω, Cash ω ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal B := by sorry
