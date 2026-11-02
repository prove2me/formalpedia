-- Prove2me | solution 1 for exists_maximal_feasible_extension_finite__p2m_53772a33_25fb_4be5_bc25_56c0a0bf34f9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:49:09.840348+00:00
-- url     : https://prove2.me/submissions/cdb4f96e-f030-457f-81e1-34cd4799285d

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} [Finite α] [PartialOrder α]
    (P : α → Prop) (a : α) (ha : P a) :
    ∃ b : α, a ≤ b ∧ P b ∧ ∀ c : α, b ≤ c → P c → c ≤ b := by
  classical
  let s : Set α := {x | P x}
  have hs : s.Finite := Set.toFinite s
  obtain ⟨b, hab, hbmax⟩ := hs.exists_le_maximal (a := a) ha
  refine ⟨b, hab, ?_, ?_⟩
  · exact hbmax.1
  · intro c hbc hc
    exact hbmax.2 hc hbc