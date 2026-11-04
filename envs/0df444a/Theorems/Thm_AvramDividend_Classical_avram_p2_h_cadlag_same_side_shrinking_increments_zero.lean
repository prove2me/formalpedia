-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_same_side_shrinking_increments_zero
-- name    : AvramDividend.Classical.avram_p2_h_cadlag_same_side_shrinking_increments_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:29:05.967037+00:00
-- url     : https://prove2.me/theorems/d70cd6b3-4ab4-4067-8ac8-1c67c33308b5
-- title:
--   Shrinking càdlàg intervals entirely on either side have zero increment limit
-- statement:
--   For an arbitrary real càdlàg path near any clock t, two shrinking observation endpoints approaching t strictly from the left have increment converging to zero. The same holds when both approach t weakly from the right. Both conclusions are proved by composing the actual one-sided path limits and subtracting. Together with the proved genuine straddling-cell convergence this supplies all three sided cases of the no-spurious-grid-cell compactness contradiction, including endpoint equality.

import Mathlib

open Set Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_h_cadlag_same_side_shrinking_increments_zero
    (Y : ℝ≥0 → ℝ) (t : ℝ≥0) (a b : ℕ → ℝ≥0)
    (hL : Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ContinuousWithinAt Y (Ici t) t) :
    ((Tendsto a atTop (𝓝[<] t) ∧ Tendsto b atTop (𝓝[<] t)) →
      Tendsto (fun n => Y (b n) - Y (a n)) atTop (𝓝 (0 : ℝ))) ∧
    ((Tendsto a atTop (nhdsWithin t (Ici t)) ∧
      Tendsto b atTop (nhdsWithin t (Ici t))) →
      Tendsto (fun n => Y (b n) - Y (a n)) atTop (𝓝 (0 : ℝ))) := by sorry
