-- Prove2me | solution 1 for exists_maximal_above_in_finite_type__p2m_0d7f4e6a_f018_419b_9ff8_3c6696d14d6d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:09:21.042932+00:00
-- url     : https://prove2.me/submissions/f55ce3ef-18b7-490e-8799-0d92cccb9a76

import Mathlib

theorem solution {α : Type} [Finite α] [PartialOrder α]
    (P : α → Prop) (a : α) (ha : P a) :
    ∃ b, P b ∧ a ≤ b ∧ ∀ c, b ≤ c → P c → c = b := by
  obtain ⟨b, hab, hb⟩ := ({x | P x}.toFinite).exists_le_maximal ha
  refine ⟨b, hb.1, hab, ?_⟩
  intro c hbc hc
  exact le_antisymm (hb.2 hc hbc) hbc