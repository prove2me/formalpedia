-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_paymentTimes_after_firstUpcrossing_eq_shifted
-- name    : AvramDividend.Classical.barrierStrategy_paymentTimes_after_firstUpcrossing_eq_shifted
-- status  : Open
-- author  : @WillR
-- created : 2026-10-21T12:10:44.676007+00:00
-- url     : https://prove2.me/theorems/28e58b97-9220-49b7-ac07-9f9fe708e0e6
-- title:
--   The payment times of the barrier strategy after the first up-crossing are the times after the up-crossing at which the drawdown has not yet breached the barrier
-- statement:
--   The integral-level consequence of the pointwise ruin identity for the barrier strategy. After the first up-crossing u of the barrier gap a - x, the reserve of the barrier strategy is negative exactly when the drawdown S - X of the process breaches the level a, so a payment time of the barrier strategy that lies after u is a payment time exactly when the drawdown of the process has not yet breached the barrier a. This is the statement needed to pass from the pointwise sign identity for the reserve to an identity of the dividends paid, and hence to the strong Markov factorisation of the barrier strategy dividend value of Proposition 1 of Avram, Palmowski and Pistorius.
-- source:
--   The integral-level form of the ruin identity for the barrier strategy, obtained from the pointwise Proved theorem riskProcess_barrier_ruin_piecewise together with the first up-crossing hypothesis. This is the step that turns the pointwise sign of the reserve into an identity of the payment times, and hence of the discounted dividends, needed for the strong Markov factorisation barrierStrategy_value_eq_killed_exit_mul_supValue of Proposition 1 of Avram, Palmowski and Pistorius, arXiv:math/0702893v1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierStrategy_paymentTimes_after_firstUpcrossing_eq_shifted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))
    (hb : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 u))
    (hdraw : ∀ t : ℝ≥0,
      riskProcess X x (barrierStrategy X x a) (u + t) ω < 0 ↔
        a < runningSup X (u + t) ω - X.X (u + t) ω) :
    {t : ℝ≥0 | u < t ∧
        (t : ℝ≥0∞) < ruinTime X x (barrierStrategy X x a) ω} =
      {t : ℝ≥0 | u < t ∧
        (t : ℝ≥0∞) < ruinTime X x (barrierStrategy X x a) ω ∧
        a < runningSup X t ω - X.X t ω} := by sorry
