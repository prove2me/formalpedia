-- Prove2me | solution 1 for finite_poset_maximal_above__p2m_cf1fad93_82bb_45b4_92ca_a77558fa3813_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:37:24.507467+00:00
-- url     : https://prove2.me/submissions/a4d544d0-7dd3-40c2-b029-c63da761eeb7

import Mathlib

theorem solution
    {α : Type} [Fintype α] [PartialOrder α]
    (P : α → Prop) {a : α} (ha : P a) :
    ∃ m, a ≤ m ∧ P m ∧ ∀ b, m ≤ b → P b → b ≤ m := by
  obtain ⟨m, ham, hm⟩ := Finite.exists_le_maximal (p := P) ha
  refine ⟨m, ham, hm.1, ?_⟩
  intro b hmb hPb
  exact hm.2 hPb hmb