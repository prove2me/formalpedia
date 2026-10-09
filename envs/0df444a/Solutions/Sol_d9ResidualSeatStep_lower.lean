-- Prove2me | solution 1 for d9ResidualSeatStep_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T14:52:24.810462+00:00
-- url     : https://prove2.me/submissions/857c1df6-8188-4b89-ab88-04c2f7af64ee

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9ClippedSeats
import Definitions.Def_d9ResidualSeatStep
import Theorems.Thm_d9ResidualSeatStep_eq_clipped
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open NestedSeatAlloc.IntPolicy
theorem solution
    (p x : ℕ → ℝ) (i : ℕ) (s : ℝ)
    (hp : 0 ≤ p i) (hx : 0 ≤ x (i + 1)) :
    s - x (i + 1) ≤ d9ResidualSeatStep p x i s := by
  rw [d9ResidualSeatStep_eq_clipped p x i s hp hx]
  have hclip : d9ClippedSeats (p i) (x (i + 1)) s ≤ x (i + 1) :=
    min_le_left _ _
  linarith
