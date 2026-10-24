-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_ruinTime_eq_min_rawRuin_drawdownRuin
-- name    : AvramDividend.Classical.barrierStrategy_ruinTime_eq_min_rawRuin_drawdownRuin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T12:22:09.781856+00:00
-- url     : https://prove2.me/theorems/b112210b-782d-4f93-a41e-fbd6180f4330
-- title:
--   The ruin time of the barrier strategy is the earlier of the ruin of the raw process and the breach of the drawdown barrier
-- statement:
--   The ruin time of the barrier strategy started at capital x with barrier a is the earlier of two events: the raw process X falling below -x, which destroys the reserve before the barrier can be reached, and the drawdown S - X of the process breaching the level a, which destroys the reserve after the barrier has been reached. This follows from the Proved pointwise identity riskProcess_barrier_ruin_piecewise, which characterises the negativity of the reserve of the barrier strategy as the disjunction of those two conditions. It is the ingredient that identifies the payment times of the barrier strategy with the times at which the shifted running supremum has not yet breached the drawdown barrier, and hence that turns the strong Markov decomposition into the factorisation of Proposition 1 of Avram, Palmowski and Pistorius.
-- source:
--   The ruin-time identity for the barrier strategy, obtained from the Proved pointwise theorem riskProcess_barrier_ruin_piecewise by passing from the sign of the reserve to the infimum of the times at which it is negative. It is the ingredient that identifies the ruin time of the barrier strategy with the earlier of the ruin of the raw process and the breach of the drawdown barrier, and hence that completes the strong Markov factorisation barrierStrategy_value_eq_killed_exit_mul_supValue of Proposition 1 of Avram, Palmowski and Pistorius, arXiv:math/0702893v1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierStrategy_ruinTime_eq_min_rawRuin_drawdownRuin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (ω : Ω) :
    ruinTime X x (barrierStrategy X x a) ω =
      min (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞))
        (⨅ (t : ℝ≥0) (_ : a < runningSup X t ω - X.X t ω), (t : ℝ≥0∞)) := by sorry
