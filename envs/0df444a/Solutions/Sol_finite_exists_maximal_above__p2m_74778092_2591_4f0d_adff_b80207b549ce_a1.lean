-- Prove2me | solution 1 for finite_exists_maximal_above__p2m_74778092_2591_4f0d_adff_b80207b549ce_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:49:46.091802+00:00
-- url     : https://prove2.me/submissions/b975d780-c529-422a-a28a-acfc9f5778f6

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} [Fintype α] [PartialOrder α]
    (P : α → Prop) (x : α) (hx : P x) :
    ∃ y, P y ∧ x ≤ y ∧ ∀ z, P z → y ≤ z → z = y := by
  obtain ⟨y, hxy, hymax⟩ := Finite.exists_le_maximal hx
  refine ⟨y, hymax.1, hxy, ?_⟩
  intro z hz hyz
  exact le_antisymm (hymax.2 hz hyz) hyz