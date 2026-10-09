-- Prove2me | solution 1 for eq30NextPayoff_eq_clipped
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T15:44:25.470037+00:00
-- url     : https://prove2.me/submissions/ce0c56dd-e355-4a86-ac0d-17bd36617fd8

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_eq30NextPayoff
import Definitions.Def_eq30ClippedSeats
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy
theorem solution
    (g : ℝ → ℝ) (p x fare s : ℝ) (hx : 0 ≤ x) :
    eq30NextPayoff g p x fare s =
      fare * eq30ClippedSeats p x s +
        g (s - eq30ClippedSeats p x s) := by
  by_cases hprotection : s < p
  · have hclip : eq30ClippedSeats p x s = 0 := by
      simp [eq30ClippedSeats, max_eq_left (by linarith : s - p ≤ 0),
        min_eq_right hx]
    simp [eq30NextPayoff, hprotection, hclip]
  · have hprotection_le : p ≤ s := le_of_not_gt hprotection
    by_cases hcapacity : s < p + x
    · have hclip : eq30ClippedSeats p x s = s - p := by
        simp [eq30ClippedSeats, max_eq_right (sub_nonneg.mpr hprotection_le),
          min_eq_right (by linarith : s - p ≤ x)]
      simp [eq30NextPayoff, hprotection, hcapacity, hclip]
      ring
    · have hcapacity_le : p + x ≤ s := le_of_not_gt hcapacity
      have hclip : eq30ClippedSeats p x s = x := by
        simp [eq30ClippedSeats, max_eq_right (sub_nonneg.mpr hprotection_le),
          min_eq_left (by linarith : x ≤ s - p)]
      simp [eq30NextPayoff, hprotection, hcapacity, hclip]
      ring
