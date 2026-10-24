-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_after_firstUpcrossing_record_increment
-- name    : AvramDividend.Classical.barrierStrategy_after_firstUpcrossing_record_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T11:56:59.498991+00:00
-- url     : https://prove2.me/theorems/35b98dc8-fbe5-47ef-8498-2a01b3a74d3f
-- title:
--   Barrier regulator after first passage equals the uncapped shifted record increment
-- statement:
--   The shifted running record includes the value X(u) at shift zero, so its supremum minus X(u) is nonnegative. Consequently, the accepted pathwise barrier restart formula has no need for max(0, ·) and the post-upcrossing dividends equal exactly the shifted running-record increment. This is an intermediate lemma for Stieltjes dividend measure translation.

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_after_firstUpcrossing_shift

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_after_firstUpcrossing_record_increment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (u t : ℝ≥0) (ω : Ω)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)))
    (hb : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 (u + t))) :
    barrierStrategy X x a (u + t) ω =
      sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) - X.X u ω := by sorry
