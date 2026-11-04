-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_shrinking_cell_increment_converges_to_actual_jump
-- name    : AvramDividend.Classical.avram_p2_34dbea70_shrinking_cell_increment_converges_to_actual_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:30:42.026609+00:00
-- url     : https://prove2.me/theorems/385951b5-5665-4439-b129-fc0e73a538e5
-- title:
--   Shrinking source cell increments converge to the genuine cadlag jump
-- statement:
--   For any actual cadlag real path and a source time u, if left and right cell endpoints converge respectively through the strict-left and weak-right neighbourhoods, the difference Y(b_n)-Y(a_n) converges to the intrinsic jump Y(u)-leftLim(Y,u). This is the source path identity needed to exclude spurious separated-magnitude negative cells in a later two-sided grid approximation. No jump-rate or process replacement assumptions are used.

import Mathlib

open Set Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_34dbea70_shrinking_cell_increment_converges_to_actual_jump
    (Y : ℝ≥0 → ℝ) (u : ℝ≥0) (a b : ℕ → ℝ≥0)
    (ha : Tendsto a atTop (𝓝[<] u))
    (hb : Tendsto b atTop (nhdsWithin u (Ici u)))
    (hL : Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u)))
    (hR : ContinuousWithinAt Y (Ici u) u) :
    Tendsto (fun n => Y (b n) - Y (a n)) atTop
      (𝓝 (Y u - Function.leftLim Y u)) := by sorry
