-- Prove2me | solution 1 for exists_maximal_witness_finite__p2m_9f3e6a97_c623_4a15_9543_38a021dd3fb9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:09:46.183098+00:00
-- url     : https://prove2.me/submissions/9578d424-b8dc-4507-bfb7-ea28d47dcc05

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} [Finite α] [PartialOrder α] (Q : α → Prop)
    (hQ : ∃ x, Q x) :
    ∃ x, Q x ∧ ∀ y, Q y → x ≤ y → y = x := by
  classical
  obtain ⟨a, ha⟩ := hQ
  obtain ⟨b, hab, hb⟩ := Finite.exists_le_maximal (p := Q) ha
  refine ⟨b, hb.1, ?_⟩
  intro y hy hby
  exact le_antisymm (hb.2 hy hby) hby