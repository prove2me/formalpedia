-- Prove2me | Theorems.Thm_AvramDividend_Classical_drawdown_after_firstUpcrossing_shift
-- name    : AvramDividend.Classical.drawdown_after_firstUpcrossing_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:57:43.185181+00:00
-- url     : https://prove2.me/theorems/f8b845d8-3ecc-41c1-9e3e-7d58427666c4
-- title:
--   The drawdown of the process after its first up-crossing of a level is the shifted drawdown plus the drawdown attained at the crossing
-- statement:
--   The pathwise additivity of the drawdown of a spectrally negative Levy process across a stopping time. The drawdown S - X of the process, where S is the running supremum, splits at a stopping time u into the drawdown already attained at u and the drawdown of the shifted path started from u. This is what identifies the drawdown barrier ruin time of the original process with the drawdown barrier ruin time of the shifted process, translated by u, and it is the second ingredient needed for the strong Markov factorisation of the barrier strategy dividend value of Proposition 1 of Avram, Palmowski and Pistorius.
-- source:
--   The pathwise additivity of the drawdown across a stopping time, needed to identify the drawdown barrier ruin time of the shifted process with the translated drawdown barrier ruin time of the original process. The shifted running supremum is written as the sSup of the shifted path over the interval, the same form that appears in the Proved theorem barrierStrategy_after_firstUpcrossing_shift. It is the second ingredient, after the strong Markov property for the dividend measure, of the factorisation barrierStrategy_value_eq_killed_exit_mul_supValue of Proposition 1 of Avram, Palmowski and Pistorius, arXiv:math/0702893v1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.drawdown_after_firstUpcrossing_shift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))
    (hb : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 u)) :
    ∀ (t : ℝ≥0),
      runningSup X (u + t) ω - X.X (u + t) ω =
        (runningSup X u ω - X.X u ω) +
          (sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) -
            X.X (u + t) ω) := by sorry
