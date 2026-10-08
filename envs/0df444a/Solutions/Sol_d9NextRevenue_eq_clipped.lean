-- Prove2me | solution 1 for d9NextRevenue_eq_clipped
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T12:54:00.560523+00:00
-- url     : https://prove2.me/submissions/0dcea635-01c8-4bad-af88-4848fe2ccf1c

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9ClippedSeats
import Definitions.Def_d9NextRevenue
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open NestedSeatAlloc.IntPolicy
theorem solution
    (g : ℝ → ℝ) (p x fare s : ℝ) (hx : 0 ≤ x) :
    d9NextRevenue g p x fare s =
      fare * d9ClippedSeats p x s +
        g (s - d9ClippedSeats p x s) := by
  by_cases hprotection : s < p
  · have hclip : d9ClippedSeats p x s = 0 := by
      simp [d9ClippedSeats, max_eq_left (by linarith : s - p ≤ 0),
        min_eq_right hx]
    simp [d9NextRevenue, hprotection, hclip]
  · have hprotection_le : p ≤ s := le_of_not_gt hprotection
    by_cases hcapacity : s < p + x
    · have hclip : d9ClippedSeats p x s = s - p := by
        simp [d9ClippedSeats, max_eq_right (sub_nonneg.mpr hprotection_le),
          min_eq_right (by linarith : s - p ≤ x)]
      simp [d9NextRevenue, hprotection, hcapacity, hclip]
      ring
    · have hcap : p + x ≤ s := le_of_not_gt hcapacity
      have hclip : d9ClippedSeats p x s = x := by
        simp [d9ClippedSeats, max_eq_right (sub_nonneg.mpr hprotection_le),
          min_eq_left (by linarith : x ≤ s - p)]
      simp [d9NextRevenue, hprotection, hcapacity, hclip]
      ring
