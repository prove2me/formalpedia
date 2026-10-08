-- Prove2me | Theorems.Thm_AvramDividend_Classical_riskProcess_post_firstUpcrossing_ruin_iff
-- name    : AvramDividend.Classical.riskProcess_post_firstUpcrossing_ruin_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:09:09.697689+00:00
-- url     : https://prove2.me/theorems/a7a95fd9-18e6-4631-9741-878d5dc1d699
-- title:
--   Pathwise post-upcrossing ruin criterion under a barrier strategy
-- statement:
--   At any finite first strict upward passage of the dividend barrier, subsequent controlled ruin at time u+t is exactly the event that the cumulative reflected dividend regulator from subsequent increments exceeds the barrier capital a plus the process increment over the same period. This translates the original capital process to the post-upcrossing excursion/drawdown inequality and provides the event-level building block for a shifted ruin-time identity. It follows by rewriting the proven post-first-upcrossing controlled-capital identity and real arithmetic, without probabilistic independence or an assumption about ruin before the passage time.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1; companion project theorem riskProcess_barrier_post_firstUpcrossing_shift.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.riskProcess_post_firstUpcrossing_ruin_iff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (u t : ℝ≥0) (ω : Ω)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)))
    (hb : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 (u + t))) :
    riskProcess X x (barrierStrategy X x a) (u + t) ω < 0 ↔
      a + (X.X (u + t) ω - X.X u ω) <
        max 0
          (sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) -
            X.X u ω) := by sorry
