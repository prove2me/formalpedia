-- Prove2me | solution 1 for finite_nonempty_has_maximal__p2m_9251ca56_2f13_4506_a97b_c72b0a41465a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:08:17.409488+00:00
-- url     : https://prove2.me/submissions/cb867ff1-ba49-4d1e-9eb5-29c942612c53

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} [Finite α] [PartialOrder α]
    (P : α → Prop) (hne : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, P b → a ≤ b → b ≤ a := by
  classical
  let s : Set α := {a | P a}
  have hs : s.Finite := Set.toFinite _
  have hsne : s.Nonempty := hne
  obtain ⟨a, ha, hmax⟩ := hs.exists_maximal hsne
  refine ⟨a, ha, ?_⟩
  intro b hb hab
  exact hmax hb hab