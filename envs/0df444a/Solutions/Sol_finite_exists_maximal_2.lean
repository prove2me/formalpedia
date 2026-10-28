-- Prove2me | solution 2 for finite_exists_maximal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T09:09:56.207629+00:00
-- url     : https://prove2.me/submissions/c3b2e522-af18-4661-87fb-889db7cc4110

import Mathlib

set_option autoImplicit false


theorem solution {α : Type} [Finite α] (P : α → Prop) (R : α → α → Prop) (hRrefl : ∀ x, R x x) (hRtrans : ∀ ⦃x y z⦄, R x y → R y z → R x z) (hP : ∃ x, P x) : ∃ x, P x ∧ ∀ y, P y → R x y → R y x := by
  classical
  letI : Preorder α := { le := R, le_refl := hRrefl, le_trans := hRtrans }
  obtain ⟨x, hx⟩ := Set.Finite.exists_maximal (Set.toFinite {x | P x}) hP
  exact ⟨x, hx.prop, fun y hy hxy => hx.2 hy hxy⟩
