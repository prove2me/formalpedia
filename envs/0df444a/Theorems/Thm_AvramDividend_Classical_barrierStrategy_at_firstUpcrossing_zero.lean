-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_at_firstUpcrossing_zero
-- name    : AvramDividend.Classical.barrierStrategy_at_firstUpcrossing_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T11:55:25.502986+00:00
-- url     : https://prove2.me/theorems/06d1bc93-16fe-476f-b9a3-89ab80aed97b
-- title:
--   No cumulative barrier dividend at its finite first upcrossing
-- statement:
--   At the finite first strict upcrossing of the barrier gap a−x, with x≤a and bounded recorded path, the cumulative barrier dividend regulator remains zero. Follows from the accepted exact pathwise post-upcrossing shift identity at time increment zero. This endpoint cancellation is essential to translating Stieltjes dividend increments on (u,u+t].

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_after_firstUpcrossing_shift

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_at_firstUpcrossing_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)))
    (hb : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 u)) :
    barrierStrategy X x a u ω = 0 := by sorry
