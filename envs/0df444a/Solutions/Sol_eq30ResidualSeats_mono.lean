-- Prove2me | solution 1 for eq30ResidualSeats_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T16:16:01.429148+00:00
-- url     : https://prove2.me/submissions/9d371e63-885d-44c8-853e-53107658c9cd

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_eq30ClippedSeats
import Theorems.Thm_eq30ClippedSeats_increment_bounds
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy
theorem solution
    (p x s t : ℝ) (hx : 0 ≤ x) (hst : s ≤ t) :
    0 ≤ (t - eq30ClippedSeats p x t) -
      (s - eq30ClippedSeats p x s) := by
  obtain ⟨_, hclip⟩ := eq30ClippedSeats_increment_bounds p x s t hx hst
  linarith
