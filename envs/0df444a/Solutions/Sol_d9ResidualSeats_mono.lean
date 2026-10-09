-- Prove2me | solution 1 for d9ResidualSeats_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T14:52:04.890615+00:00
-- url     : https://prove2.me/submissions/ebf8a455-6760-4b49-860b-23a883ff4e3c

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9ClippedSeats
import Theorems.Thm_d9ClippedSeats_increment_bounds
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open NestedSeatAlloc.IntPolicy
theorem solution
    (p x s t : ℝ) (hx : 0 ≤ x) (hst : s ≤ t) :
    0 ≤ (t - d9ClippedSeats p x t) - (s - d9ClippedSeats p x s) := by
  obtain ⟨_, hclip⟩ := d9ClippedSeats_increment_bounds p x s t hx hst
  linarith
