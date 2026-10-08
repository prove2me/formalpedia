-- Prove2me | solution 1 for d9ResidualSeatStep_eq_clipped
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T12:27:30.869261+00:00
-- url     : https://prove2.me/submissions/ab9ae7ef-789c-413d-9e52-f6c3cc0644a7

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9ClippedSeats
import Definitions.Def_d9ResidualSeatStep
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open NestedSeatAlloc.IntPolicy
theorem solution
    (p x : ℕ → ℝ) (i : ℕ) (s : ℝ)
    (hp : 0 ≤ p i) (hx : 0 ≤ x (i + 1)) :
    d9ResidualSeatStep p x i s =
      s - d9ClippedSeats (p i) (x (i + 1)) s := by
  by_cases hprotection : s < p i
  · have hclip : d9ClippedSeats (p i) (x (i + 1)) s = 0 := by
      simp [d9ClippedSeats, max_eq_left (sub_nonpos.mpr (le_of_lt hprotection)),
        min_eq_right hx]
    simp [d9ResidualSeatStep, hprotection, hclip]
  · have hps : p i ≤ s := le_of_not_gt hprotection
    by_cases hcapacity : s < p i + x (i + 1)
    · have hclip : d9ClippedSeats (p i) (x (i + 1)) s = s - p i := by
        simp [d9ClippedSeats, max_eq_right (sub_nonneg.mpr hps),
          min_eq_right (by linarith : s - p i ≤ x (i + 1))]
      simp [d9ResidualSeatStep, hprotection, hcapacity, hclip]

    · have hcap : p i + x (i + 1) ≤ s := le_of_not_gt hcapacity
      have hclip : d9ClippedSeats (p i) (x (i + 1)) s = x (i + 1) := by
        simp [d9ClippedSeats, max_eq_right (sub_nonneg.mpr (by linarith : p i ≤ s)),
          min_eq_left (by linarith : x (i + 1) ≤ s - p i)]
      simp [d9ResidualSeatStep, hprotection, hcapacity, hclip]
