-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_dividend_window_real_lintegral_bridge
-- name    : AvramDividend.Classical.discounted_dividend_window_real_lintegral_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:07:43.534475+00:00
-- url     : https://prove2.me/theorems/dc3d2d98-a7a6-449c-8d85-780496c7c6d2
-- title:
--   The actual finite-horizon stopped dividend payout is an embedded real Stieltjes integral
-- statement:
--   For an actual monotone finite-valued dividend strategy, any stopped nonnegative payment window and a nonnegative discount rate, the extended-real Stieltjes payoff equals the ENNReal embedding of its ordinary real-valued Lebesgue–Stieltjes integral. Finite-measure integrability follows automatically from the original strategy through the exact [0,T+1) dividend mass identity. This removes artificial integrability hypotheses from the stochastic chain-rule handoff.

import Theorems.Thm_AvramDividend_Classical_discounted_stieltjes_finite_measure_payout_bridge
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ico_zero_eq_dividendValue
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Mathlib.Tactic.NormNum

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.discounted_dividend_window_real_lintegral_bridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : ℝ≥0∞) (T : ℝ≥0) (ω : Ω) :
    (∫⁻ t in paymentTimes σ ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      ENNReal.ofReal
        (∫ t in paymentTimes σ ∩ Iic (T : ℝ),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) := by sorry
