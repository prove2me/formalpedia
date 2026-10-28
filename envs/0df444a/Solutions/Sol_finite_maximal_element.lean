-- Prove2me | solution 1 for finite_maximal_element
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:37:32.106444+00:00
-- url     : https://prove2.me/submissions/4058d3d0-f778-4f09-a0cd-b3101f540693

import Mathlib

set_option autoImplicit false
theorem solution
    {α : Type} [Fintype α]
    (P : α → Prop) (R : α → α → Prop) (rank : α → Nat) (a : α)
    (ha : P a)
    (hbase : ∀ b, P b → R a b) :
    ∃ b, P b ∧ R a b ∧ ∀ c, P c → rank c ≤ rank b := by
  classical
  obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image (Finset.univ.filter P) rank
    ⟨a, by simp [ha]⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb hmax
  exact ⟨b, hb, hbase b hb, fun c hc => hmax c hc⟩
