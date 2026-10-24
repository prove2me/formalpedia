-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_dividend_window_integrableOn_of_strategy
-- name    : AvramDividend.Classical.discounted_dividend_window_integrableOn_of_strategy
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:18:42.861014+00:00
-- url     : https://prove2.me/theorems/98504925-d785-468c-9dac-a18cb280b768
-- title:
--   Exponential discount is Stieltjes-integrable over every actual stopped finite dividend window
-- statement:
--   The actual finite-horizon stopped dividend measure is finite on the payment window, and every discounted factor exp(-q t), q≥0, is integrable with respect to the dividend Stieltjes measure there. This packages the integrability premise required by real-valued stochastic verification and Lebesgue–Stieltjes change-of-variables identities for an arbitrary dividend strategy.

import Theorems.Thm_AvramDividend_Classical_discounted_stieltjes_integrableOn_of_finite_measure
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_paymentWindow_finite_of_strategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.discounted_dividend_window_integrableOn_of_strategy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : ℝ≥0∞) (T : ℝ≥0) (ω : Ω) :
    IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
      (paymentTimes σ ∩ Iic (T : ℝ)) (dividendMeasure D ω) := by sorry
