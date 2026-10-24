-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_preRuin_drawdown_le_of_risk_iff
-- name    : AvramDividend.Classical.barrierStrategy_preRuin_drawdown_le_of_risk_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T16:51:34.550586+00:00
-- url     : https://prove2.me/theorems/09ba408e-4c41-42e9-8d1f-24192b82cf8e
-- title:
--   Before barrier ruin the drawdown cannot exceed the barrier
-- statement:
--   Suppose the barrier-controlled reserve at the shifted time u+t is negative exactly when the running-supremum drawdown exceeds the barrier a. If u+t lies strictly before the controlled ruin time, then the reserve is nonnegative by the proved pre-ruin lemma, hence the drawdown is at most a. This is the correct support condition for the first-upcrossing payment region, and exposes why the existing open set identity which adds a strict drawdown exceedance inside a pre-ruin payment-time set is inconsistent.
-- source:
--   Deduction from Proved riskProcess_nonnegative_strictly_before_ruin (03a69d71), using the same hdraw hypothesis as Open barrierStrategy_paymentTimes_after_firstUpcrossing_eq_shifted (28e58b97).

import Theorems.Thm_AvramDividend_Classical_riskProcess_nonnegative_strictly_before_ruin
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierStrategy_preRuin_drawdown_le_of_risk_iff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ)
    (ω : Ω) (u t : ℝ≥0)
    (hdraw : riskProcess X x (barrierStrategy X x a) (u + t) ω < 0 ↔
      a < runningSup X (u + t) ω - X.X (u + t) ω)
    (hbefore : ((u + t : ℝ≥0) : ℝ≥0∞) <
      ruinTime X x (barrierStrategy X x a) ω) :
    runningSup X (u + t) ω - X.X (u + t) ω ≤ a := by sorry
