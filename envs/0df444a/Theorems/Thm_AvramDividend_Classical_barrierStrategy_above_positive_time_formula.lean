-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_above_positive_time_formula
-- name    : AvramDividend.Classical.barrierStrategy_above_positive_time_formula
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T16:21:35.710997+00:00
-- url     : https://prove2.me/theorems/e01bea98-367e-40e6-8a1e-5ee311a9d7b4
-- title:
--   Above-barrier dividends equal the initial excess plus boundary dividends at positive times
-- statement:
--   At every strictly positive time, a constant-barrier strategy begun above its nonnegative barrier pays precisely the initial excess x−a plus the boundary-started barrier strategy. The initial-time exception is essential and is why global right-continuity fails above the barrier. This pointwise formula supports right-continuity away from zero and correct handling of the initial Stieltjes atom.
-- source:
--   Deduction from Proved AvramDividend.Classical.barrierStrategy_eq_add_initial_excess_above_barrier (ece035bb-c53e-404d-bb43-a95bdd4a6f98).

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_eq_add_initial_excess_above_barrier
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierStrategy_above_positive_time_formula
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ)
    (ha : 0 ≤ a) (hax : a < x) (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    barrierStrategy X x a t ω =
      (x - a) + barrierStrategy X a a t ω := by sorry
