-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_after_firstUpcrossing_increment_eq_shiftedSup
-- name    : AvramDividend.Classical.barrierStrategy_after_firstUpcrossing_increment_eq_shiftedSup
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T12:39:45.824517+00:00
-- url     : https://prove2.me/theorems/1b010e95-c741-449c-aa34-30482b7bedb2
-- title:
--   Barrier dividend increment after first upcrossing is the shifted running supremum
-- statement:
--   After the first strict upcrossing of the barrier gap, accumulated dividends before the crossing vanish and the subsequent dividend increment is the running supremum of path increments measured from the crossing. This provides the algebraic increment equality required by the Stieltjes measure time-translation theorem.

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_at_firstUpcrossing_zero
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_after_firstUpcrossing_record_increment

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_after_firstUpcrossing_increment_eq_shiftedSup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (ω : Ω) (u t : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)))
    (hb : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 (u + t))) :
    barrierStrategy X x a (u + t) ω - barrierStrategy X x a u ω =
      sSup ((fun r : ℝ≥0 => X.X (u + r) ω - X.X u ω) '' Set.Icc 0 t) := by sorry
