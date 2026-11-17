-- Prove2me | solution 1 for d9ResidualSeatStep_continuous
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:39:02.744203+00:00
-- url     : https://prove2.me/submissions/9a4025a9-405d-4912-bf17-fceed6ea8143

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9ClippedSeats
import Definitions.Def_d9ResidualSeatStep
import Theorems.Thm_d9ResidualSeatStep_eq_clipped
open NestedSeatAlloc.IntPolicy

theorem d9ResidualSeatStep_continuous
    (p x : ℕ → ℝ) (i : ℕ)
    (hp : 0 ≤ p i) (hx : 0 ≤ x (i + 1)) :
    Continuous (fun s => d9ResidualSeatStep p x i s) := by
  have h : (fun s => d9ResidualSeatStep p x i s) =
      fun s => min s (p i) + max 0 (s - p i - x (i + 1)) := by
    funext s
    unfold d9ResidualSeatStep
    split_ifs with h1 h2
    · rw [min_eq_left h1.le, max_eq_left (by linarith)]; ring
    · rw [min_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [min_eq_right (by linarith), max_eq_right (by linarith)]; ring
  rw [h]
  exact (continuous_id.min continuous_const).add
    (continuous_const.max ((continuous_id.sub continuous_const).sub continuous_const))

theorem solution
    (p x : ℕ → ℝ) (i : ℕ)
    (hp : 0 ≤ p i) (hx : 0 ≤ x (i + 1)) :
    Continuous (fun s => d9ResidualSeatStep p x i s) := by
  have h : (fun s => d9ResidualSeatStep p x i s) =
      fun s => min s (p i) + max 0 (s - p i - x (i + 1)) := by
    funext s
    unfold d9ResidualSeatStep
    split_ifs with h1 h2
    · rw [min_eq_left h1.le, max_eq_left (by linarith)]; ring
    · rw [min_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [min_eq_right (by linarith), max_eq_right (by linarith)]; ring
  rw [h]
  exact (continuous_id.min continuous_const).add
    (continuous_const.max ((continuous_id.sub continuous_const).sub continuous_const))


