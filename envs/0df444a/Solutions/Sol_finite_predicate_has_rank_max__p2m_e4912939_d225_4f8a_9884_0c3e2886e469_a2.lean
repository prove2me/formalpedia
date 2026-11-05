-- Prove2me | solution 1 for finite_predicate_has_rank_max__p2m_e4912939_d225_4f8a_9884_0c3e2886e469_a2
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T16:15:51.198077+00:00
-- url     : https://prove2.me/submissions/c42334e2-18c1-45fc-9235-94020cb6bafc

import Mathlib

theorem solution {α : Type} [Fintype α] (P : α → Prop) (rank : α → Nat)
    (a : α) (ha : P a) : ∃ b, P b ∧ ∀ c, P c → rank c ≤ rank b := by
  classical
  let s : Finset α := Finset.univ.filter P
  have hs : s.Nonempty := ⟨a, by simp [s, ha]⟩
  obtain ⟨b, hbs, hbmax⟩ := Finset.exists_max_image s rank hs
  refine ⟨b, ?_, ?_⟩
  · simpa [s] using hbs
  · intro c hc
    exact hbmax c (by simp [s, hc])
