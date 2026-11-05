-- Prove2me | solution 1 for finite_partial_order_has_maximal_above__p2m_b64ec28e_2554_405c_95cb_8078e84c56ed_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T16:16:23.339191+00:00
-- url     : https://prove2.me/submissions/4ffa9333-dad4-495b-a11e-4a34e11c96de

import Mathlib

theorem solution {α : Type} [PartialOrder α] [Finite α] (a : α) :
    ∃ b : α, a ≤ b ∧ ∀ c : α, b ≤ c → c = b := by
  obtain ⟨b, hab, hbmax⟩ :=
    (Finite.exists_le_maximal (α := α) (p := fun _ : α => True) (a := a) trivial)
  refine ⟨b, hab, ?_⟩
  intro c hbc
  exact (le_antisymm hbc (hbmax.2 trivial hbc)).symm
