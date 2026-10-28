-- Prove2me | Theorems.Thm_AvramDividend_Classical_surviving_stopped_unit_cash_integrable_of_integrable_levy_reserve
-- name    : AvramDividend.Classical.surviving_stopped_unit_cash_integrable_of_integrable_levy_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T22:24:28.279478+00:00
-- url     : https://prove2.me/theorems/7fd6635e-625b-4761-b9ee-558b60de8d0c
-- title:
--   Integrable surviving stopped Stieltjes cash on each unit interval
-- statement:
--   For a dividend strategy, stopped Stieltjes payments within each deterministic half-open unit interval and before finite horizon T, restricted to paths surviving strictly beyond S>T, have an integrable real cash value whenever x+X_S is integrable. The preceding Proved surviving finite-expectation cash-block theorem gives the ENNReal first-moment bound. Stopped cash measurability, ruin-time measurability, and the equivalence between a finite nonnegative lintegral and real integrability yield the result. This supplies the precise surviving-side hCashI moment hypothesis for localisation in the capped BV/UV verification branch, with ruin-before-S handled separately.

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_stopped_discounted_unit_cash_measurable_of_strategy
import Theorems.Thm_AvramDividend_Classical_surviving_stopped_unit_cash_expected_finite_of_integrable_levy_reserve

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.surviving_stopped_unit_cash_integrable_of_integrable_levy_reserve
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q)
    (T S : ℝ≥0) (hTS : T < S)
    (hXI : Integrable (fun ω => x + X.X S ω) P)
    (k : ℕ) :
    Integrable (fun ω : Ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        (∫⁻ r in
          (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) ∩
            Ico (k : ℝ) ((k : ℝ) + 1),
          ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)).toReal
      else 0) P := by sorry
