-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_jump_tail_pushforward
-- name    : AvramDividend.Classical.negative_jump_tail_pushforward
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T23:45:37.301527+00:00
-- url     : https://prove2.me/theorems/997fd8f4-733c-4afb-aa55-38b57101f4c6
-- title:
--   Negative Lévy-jump tail equals the positive jump-magnitude pushforward tail
-- statement:
--   For any measure ν on real jump sizes and positive threshold t, push ν forward by y↦max(-y,0) into nonnegative jump magnitudes. Then the pushforward tail above t equals the original mass of jumps y<-t. This exact identity identifies the positive renewal kernel K(t)=q+ν((−∞,−t)) with the positive-jump-magnitude tail used by the already-proved layer-cake and Laplace-transform theorems. It requires no extra stochastic or finite-variation assumptions.
-- source:
--   Mathlib MeasureTheory.Measure.map_apply and Real.coe_toNNReal' at pinned 0df444a360, actual Avram Classical negative-jump Lévy measure

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- The positive jump-magnitude image of a real Lévy jump measure has
tail μ{z : t < z} equal to the original negative-jump tail ν(-∞,-t)
at every strictly positive threshold t. -/
theorem negative_jump_tail_pushforward (ν : Measure ℝ) (t : ℝ) (ht : 0 < t) :
    (Measure.map (fun y : ℝ => Real.toNNReal (-y)) ν)
      {z : ℝ≥0 | t < (z : ℝ)} = ν (Iio (-t)) := by
  sorry

end AvramDividend.Classical
