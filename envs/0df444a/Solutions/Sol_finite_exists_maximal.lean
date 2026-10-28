-- Prove2me | solution 1 for finite_exists_maximal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T09:09:49.340981+00:00
-- url     : https://prove2.me/submissions/733c6c01-d316-4e39-b1af-589aebb49c6e

import Mathlib

set_option autoImplicit false


theorem solution {α : Type} [Finite α] (P : α → Prop) (R : α → α → Prop) (hRrefl : ∀ x, R x x) (hRtrans : ∀ ⦃x y z⦄, R x y → R y z → R x z) (hP : ∃ x, P x) : ∃ x, P x ∧ ∀ y, P y → R x y → R y x := by
  classical
  letI : Preorder α := { le := R, le_refl := hRrefl, le_trans := hRtrans }
  obtain ⟨x, hx⟩ := Set.Finite.exists_maximal (Set.toFinite {x | P x}) hP
  exact ⟨x, hx.prop, fun y hy hxy => hx.2 hy hxy⟩
