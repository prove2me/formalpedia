-- Prove2me | solution 1 for exists_maximal_of_finite_family__p2m_76ca258b_4f2e_4801_9d46_2c2421541685_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:41:28.459941+00:00
-- url     : https://prove2.me/submissions/52419964-2862-4dfd-b3eb-72d9b0b8279c

import Mathlib
set_option autoImplicit false

theorem solution {α : Type} [Finite α] [PartialOrder α] (P : α → Prop) (hP : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, P b → a ≤ b → b ≤ a := by
  classical
  let S : Set α := {a | P a}
  have hS : S.Nonempty := by
    rcases hP with ⟨a, ha⟩
    exact ⟨a, ha⟩
  obtain ⟨a, ha⟩ := S.toFinite.exists_maximal hS
  refine ⟨a, ?_⟩
  simpa [S, Maximal] using ha