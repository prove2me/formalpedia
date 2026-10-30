-- Prove2me | solution 1 for finite_partial_order_maximal_extension__p2m_c7432618_08fc_4a77_9546_40c80146e77b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:18:26.415743+00:00
-- url     : https://prove2.me/submissions/8c04eca6-f6a9-490a-9c97-f473447abddc

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} [Finite α] [PartialOrder α]
    (P : α → Prop) (x : α) (hPx : P x) :
    ∃ y : α, x ≤ y ∧ P y ∧
      ∀ z : α, y ≤ z → P z → z = y := by
  classical
  let s : Set α := {y | P y}
  have hs : s.Finite := Set.toFinite s
  obtain ⟨y, hxy, hymax⟩ := hs.exists_le_maximal (a := x) (by simpa [s] using hPx)
  refine ⟨y, hxy, hymax.1, ?_⟩
  intro z hyz hPz
  exact le_antisymm (hymax.2 hPz hyz) hyz