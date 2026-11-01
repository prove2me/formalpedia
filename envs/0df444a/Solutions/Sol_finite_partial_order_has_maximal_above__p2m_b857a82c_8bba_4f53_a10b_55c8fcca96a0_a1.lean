-- Prove2me | solution 1 for finite_partial_order_has_maximal_above__p2m_b857a82c_8bba_4f53_a10b_55c8fcca96a0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:43:41.756483+00:00
-- url     : https://prove2.me/submissions/767db7b0-8d75-43b3-86c6-2682c7338779

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} [PartialOrder α] [Finite α]
    (P : α → Prop) (a : α) (ha : P a) :
    ∃ b, a ≤ b ∧ P b ∧ ∀ c, b ≤ c → P c → c = b := by
  classical
  obtain ⟨b, hab, hbmax⟩ :=
    (Set.toFinite {x : α | P x}).exists_le_maximal
      (show a ∈ {x : α | P x} from ha)
  refine ⟨b, hab, hbmax.1, ?_⟩
  intro c hbc hc
  exact le_antisymm (hbmax.2 hc hbc) hbc