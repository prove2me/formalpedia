-- Prove2me | solution 1 for finite_preorder_has_maximal__p2m_d50bd5f9_430a_4ac6_90e0_7716421734c3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:02:26.196194+00:00
-- url     : https://prove2.me/submissions/2c9d3723-5387-47be-9a35-2b80b993450e

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} [Preorder α] [Finite α]
    (P : α → Prop) (hne : ∃ x, P x) :
    ∃ x, P x ∧ ∀ y, P y → x ≤ y → y ≤ x := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨b, _, hb⟩ := Finite.exists_le_maximal (p := P) ha
  exact ⟨b, hb.1, hb.2⟩