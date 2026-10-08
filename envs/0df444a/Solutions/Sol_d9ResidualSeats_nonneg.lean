-- Prove2me | solution 1 for d9ResidualSeats_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T12:27:16.80888+00:00
-- url     : https://prove2.me/submissions/0a172960-eb34-4788-9dc7-debc0bf0cbc0

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9ClippedSeats
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open NestedSeatAlloc.IntPolicy
theorem solution
    (p x s : ℝ) (hp : 0 ≤ p) (hs : 0 ≤ s) :
    0 ≤ s - d9ClippedSeats p x s := by
  have hmax : max 0 (s - p) ≤ s :=
    max_le_iff.mpr ⟨hs, by linarith⟩
  have hc : d9ClippedSeats p x s ≤ max 0 (s - p) := min_le_right _ _
  dsimp [d9ClippedSeats] at hc ⊢
  linarith
