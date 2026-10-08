-- Prove2me | Theorems.Thm_AvramDividend_Classical_riskProcess_barrier_post_firstUpcrossing_shift
-- name    : AvramDividend.Classical.riskProcess_barrier_post_firstUpcrossing_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:04:50.643012+00:00
-- url     : https://prove2.me/theorems/6faad50b-200b-4db0-8aed-cec35e7b8759
-- title:
--   Controlled surplus after first barrier crossing in shifted increments
-- statement:
--   The controlled reserve at time u+t after a finite first strict upward crossing u of a−x equals the barrier initial reserve a plus the subsequent increment X_(u+t)−X_u, less the dividend regulator constructed from the running supremum of post-u increments. This follows algebraically from the original controlled surplus x+X−L, from exact attainment X_u=a−x, and from the post-first-upcrossing pathwise dividend shift formula. It describes the post-crossing drawdown process without invoking a stopped strong-Markov law. The next step is to identify shifted ruin and discount-stopped dividend measures.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 1, reflected process description; canonical Proved firstUpcrossing_attains_peak and published barrierStrategy_after_firstUpcrossing_shift.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.riskProcess_barrier_post_firstUpcrossing_shift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (u t : ℝ≥0) (ω : Ω)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)))
    (hb : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 (u + t))) :
    riskProcess X x (barrierStrategy X x a) (u + t) ω =
      a + (X.X (u + t) ω - X.X u ω) -
        max 0
          (sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) -
            X.X u ω) := by sorry
