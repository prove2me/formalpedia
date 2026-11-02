-- Prove2me | solution 1 for finite_downward_closed_has_maximal_extension__p2m_10545618_b4b5_4074_9cf5_b3ff4c8d7112_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:59:52.791781+00:00
-- url     : https://prove2.me/submissions/00c38898-a409-4ce4-b4a3-2a1ef2a4cd7a

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} [Fintype α] [PartialOrder α]
    (P : α → Prop)
    (hdown : ∀ {x y : α}, x ≤ y → P y → P x)
    (a : α) (ha : P a) :
    ∃ b : α, a ≤ b ∧ P b ∧ ∀ c : α, b ≤ c → P c → c ≤ b := by
  let s : Set α := {x | P x}
  have hs : s.Finite := Set.finite_univ.subset (Set.subset_univ s)
  have ha' : a ∈ s := ha
  obtain ⟨b, hab, hbmax⟩ := hs.exists_le_maximal ha'
  refine ⟨b, hab, hbmax.1, ?_⟩
  intro c hbc hc
  exact hbmax.2 hc hbc