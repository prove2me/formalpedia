-- Prove2me | solution 1 for exists_maximal_element_of_finite__p2m_30ea4785_5bd8_46ba_aa70_67a6b8ccdea6_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:53:44.398829+00:00
-- url     : https://prove2.me/submissions/b4866353-eec4-47d2-8ff6-d6d41a11c957

import Mathlib

theorem solution
    {α : Type} [Fintype α] [PartialOrder α]
    (P : α → Prop) (a : α) (ha : P a) :
    ∃ m : α, P m ∧ a ≤ m ∧ ∀ k : α, m ≤ k → P k → k = m := by
  obtain ⟨m, ⟨h1, h2⟩, h3⟩ := Set.Finite.exists_maximal (s := {x : α | P x ∧ a ≤ x}) (Set.toFinite _) ⟨a, ha, le_rfl⟩
  exact ⟨m, h1, h2, fun k hk hPk => le_antisymm (h3 ⟨hPk, le_trans h2 hk⟩ hk) hk⟩
