-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_straddling_cell_detects_negative_jump
-- name    : AvramDividend.Classical.avram_p2_34dbea70_straddling_cell_detects_negative_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:00:31.22977+00:00
-- url     : https://prove2.me/theorems/5a8809f9-dc9d-406e-930b-88f0367c8c67
-- title:
--   A genuine negative cadlag jump is eventually visible to any straddling shrinking grid cells
-- statement:
--   For a real-valued path with the actual strict left limit and right-continuity at a positive jump time, if time-cell left endpoints approach strictly from the left and right endpoints approach from the right, a jump at most minus epsilon is eventually detected by a cell increment strictly below minus epsilon over two. This pure pathwise lemma is needed for finite-subset grid capture of the original intrinsic Levy jump count and assumes neither a compensator nor a rate identity.

import Mathlib

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_34dbea70_straddling_cell_detects_negative_jump
    (Y : ℝ≥0 → ℝ) (u : ℝ≥0) (a b : ℕ → ℝ≥0)
    (ha : Tendsto a atTop (𝓝[<] u))
    (hb : Tendsto b atTop (nhdsWithin u (Ici u)))
    (hLeft : Tendsto Y (𝓝[<] u)
      (𝓝 (Function.leftLim Y u)))
    (hRight : ContinuousWithinAt Y (Ici u) u)
    (ε : ℝ) (hε : 0 < ε)
    (hJump : Y u - Function.leftLim Y u ≤ -ε) :
    ∀ᶠ n : ℕ in atTop, Y (b n) - Y (a n) < -ε / 2 := by sorry
