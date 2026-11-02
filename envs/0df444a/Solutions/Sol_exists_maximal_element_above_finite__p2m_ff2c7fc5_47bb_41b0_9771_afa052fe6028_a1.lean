-- Prove2me | solution 1 for exists_maximal_element_above_finite__p2m_ff2c7fc5_47bb_41b0_9771_afa052fe6028_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:13:21.274119+00:00
-- url     : https://prove2.me/submissions/02b31317-f740-48e0-b75f-8e3b28d63094

import Mathlib

theorem solution
    {α : Type} [Fintype α] [PartialOrder α] (P : α → Prop) (a : α) (ha : P a) :
    ∃ b : α, a ≤ b ∧ P b ∧ ∀ c : α, b ≤ c → P c → c = b := by
  classical
  let s : Set α := {x | P x}
  have hs : s.Finite := Set.toFinite s
  obtain ⟨b, hab, hb, hmax⟩ := hs.exists_le_maximal (a := a) (by simpa [s] using ha)
  refine ⟨b, hab, ?_, ?_⟩
  · simpa [s] using hb
  · intro c hbc hc
    exact le_antisymm (hmax (by simpa [s] using hc) hbc) hbc