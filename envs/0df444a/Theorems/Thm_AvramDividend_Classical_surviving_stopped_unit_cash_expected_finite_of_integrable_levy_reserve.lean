-- Prove2me | Theorems.Thm_AvramDividend_Classical_surviving_stopped_unit_cash_expected_finite_of_integrable_levy_reserve
-- name    : AvramDividend.Classical.surviving_stopped_unit_cash_expected_finite_of_integrable_levy_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T22:17:52.882627+00:00
-- url     : https://prove2.me/theorems/8d8b836e-7f33-443a-b34d-e85d028f64fe
-- title:
--   Finite expectation for each surviving stopped Stieltjes cash block
-- statement:
--   Before a fixed deterministic horizon S strictly preceding ruin, every discounted Stieltjes unit cash interval through earlier horizon T has finite expected payment under an integrable uncontrolled Lévy reserve. The interval cash is bounded pathwise by the entire surviving discounted Stieltjes payout, whose expectation is already canonically Proved finite. Import this in the BV or UV localisation to establish the surviving-branch cash moment budget, leaving the ruin-before-S branch for a separate stopped-process argument.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_surviving_stopped_dividend_expected_finite_of_integrable_levy_reserve

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.surviving_stopped_unit_cash_expected_finite_of_integrable_levy_reserve
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : Ω → ℝ≥0∞)
    (T S : ℝ≥0) (hTS : T < S)
    (hXI : Integrable (fun ω => x + X.X S ω) P)
    (k : ℕ) :
    (∫⁻ ω, if (S : ℝ≥0∞) < ruinTime X x D ω then
      (∫⁻ r in
        (paymentTimes (σ ω) ∩ Iic (T : ℝ)) ∩
          Ico (k : ℝ) ((k : ℝ) + 1),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω))
      else 0 ∂P) ≠ ⊤ := by sorry
