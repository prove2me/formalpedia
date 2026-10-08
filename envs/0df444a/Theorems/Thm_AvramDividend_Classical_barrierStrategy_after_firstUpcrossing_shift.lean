-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_after_firstUpcrossing_shift
-- name    : AvramDividend.Classical.barrierStrategy_after_firstUpcrossing_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:54:29.427477+00:00
-- url     : https://prove2.me/theorems/45c142a6-d973-4377-b915-fde631802cfd
-- title:
--   Barrier dividend regulator restarts from shifted increments at first upward passage
-- statement:
--   At a finite first strict upward crossing u of the level a−x, a spectrally negative Lévy path has both X_u=a−x and X_u equal to its running supremum up to u. These pathwise facts, established by firstUpcrossing_attains_peak, are precisely the hypotheses of the Proved post-peak barrier regulator shift formula. Therefore, at any later time u+t the cumulative barrier dividends are the nonnegative excess of the running supremum of the shifted path over the attained X_u, provided the path is bounded above on [0,u+t]. This gives the exact pathwise dividend restart formula required before invoking a stopped strong-Markov law. All substantive dependencies are already Proved.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 1; canonical Proved AvramDividend.Classical.firstUpcrossing_attains_peak and barrierStrategy_after_attained_threshold_shift.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_after_firstUpcrossing_shift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (u t : ℝ≥0) (ω : Ω)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)))
    (hb : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 (u + t))) :
    barrierStrategy X x a (u + t) ω =
      max 0
        (sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) -
          X.X u ω) := by sorry
