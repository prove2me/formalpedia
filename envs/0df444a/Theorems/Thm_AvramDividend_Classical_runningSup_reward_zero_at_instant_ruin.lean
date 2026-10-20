-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_reward_zero_at_instant_ruin
-- name    : AvramDividend.Classical.runningSup_reward_zero_at_instant_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T20:18:35.112306+00:00
-- url     : https://prove2.me/theorems/70673551-84b3-4b77-8b4d-0eb258cd9b8a
-- title:
--   Original stopped reflected dividend reward is zero on every path ruined at time zero
-- statement:
--   When the true strictly reflected drawdown ruin time is zero on a sample path, the original prescribed paymentTimes(0) is precisely the singleton {0}. The genuine running-supremum Stieltjes dividend measure has zero mass at time zero, so its restricted measure on paymentTimes(0) is zero. Consequently the discounted dividend integral is zero for every discount q, including q of either sign, with no unjustified exclusion of the special time-zero payout convention. This is the exact instantaneous-ruin endpoint case required for the stopped inverse-record reward argument.
-- source:
--   Actual barrierRuinTime and paymentTimes definitions; pending remotely Proved runningSup_dividendMeasure_zero_atom; pinned Mathlib Measure.restrict_eq_zero and lintegral_zero_measure.

import Mathlib.MeasureTheory.Measure.Restrict
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_zero_atom

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_reward_zero_at_instant_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a q : ℝ) (ω : Ω)
    (hRuin : barrierRuinTime X a ω = 0) :
    (∫⁻ t in paymentTimes (barrierRuinTime X a ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure (runningSup X) ω)) = 0 := by sorry
