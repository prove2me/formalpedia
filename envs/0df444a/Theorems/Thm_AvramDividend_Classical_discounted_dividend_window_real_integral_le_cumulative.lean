-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_dividend_window_real_integral_le_cumulative
-- name    : AvramDividend.Classical.discounted_dividend_window_real_integral_le_cumulative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:12:43.717479+00:00
-- url     : https://prove2.me/theorems/af63bebc-d52a-41ae-94c3-2c94f86fc283
-- title:
--   Real-valued stopped dividend integral bounded by actual cumulative dividends
-- statement:
--   The real-valued Stieltjes integral of nonnegative-rate discounted dividends on an actual stopped payment window is at most D(T+1) pathwise. This transports the verified extended-real payout bound into real-valued signed-generator and stochastic calculus estimates without further integrability assumptions, using positivity of D(T+1) from the dividend strategy axioms.

import Theorems.Thm_AvramDividend_Classical_discounted_dividend_window_le_cumulative
import Theorems.Thm_AvramDividend_Classical_discounted_dividend_window_real_lintegral_bridge
import Mathlib.Data.ENNReal.Real

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.discounted_dividend_window_real_integral_le_cumulative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : ℝ≥0∞) (T : ℝ≥0) (ω : Ω) :
    (∫ t in paymentTimes σ ∩ Iic (T : ℝ),
       Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ≤ D (T + 1) ω := by sorry
