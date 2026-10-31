-- Prove2me | solution 1 for finite_nonempty_has_maximal__p2m_4ded7af1_c0ed_47aa_b513_64b98071a5c3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:11:45.71334+00:00
-- url     : https://prove2.me/submissions/199c394b-a545-4f0c-b98d-1c8f2fb0b42c

import Mathlib

theorem solution {α : Type} [Fintype α] [PartialOrder α] (P : α → Prop)
    (hP : ∃ a, P a) : ∃ a, P a ∧ ∀ b, P b → a ≤ b → b ≤ a := by
  classical
  let s : Set α := {a | P a}
  have hs : s.Finite := Set.toFinite s
  obtain ⟨seed, hseed⟩ := hP
  have hs_nonempty : s.Nonempty := ⟨seed, hseed⟩
  obtain ⟨m, hm⟩ := hs.exists_maximal hs_nonempty
  refine ⟨m, hm.1, ?_⟩
  intro b hb hmb
  exact hm.2 hb hmb