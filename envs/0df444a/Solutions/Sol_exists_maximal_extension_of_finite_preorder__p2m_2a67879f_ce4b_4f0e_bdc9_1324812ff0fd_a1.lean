-- Prove2me | solution 1 for exists_maximal_extension_of_finite_preorder__p2m_2a67879f_ce4b_4f0e_bdc9_1324812ff0fd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T08:55:27.210039+00:00
-- url     : https://prove2.me/submissions/ccfa98e6-d1ac-4fc2-af39-a9975a013b25

import Mathlib

set_option autoImplicit false

theorem solution {α : Type} [Finite α] (r : α → α → Prop) (hrefl : ∀ a, r a a) (htrans : ∀ {a b c}, r a b → r b c → r a c) (P : α → Prop) (a : α) (ha : P a) : ∃ b, r a b ∧ P b ∧ ∀ c, r b c → P c → r c b := by
  classical
  have := Fintype.ofFinite α
  let S : Finset α := Finset.univ.filter (fun b => r a b ∧ P b)
  have hS : S.Nonempty := ⟨a, by simp [S, hrefl a, ha]⟩
  let up : α → Finset α := fun b => Finset.univ.filter (fun c => r b c)
  obtain ⟨b, hbS, hmin⟩ := Finset.exists_min_image S (fun b => (up b).card) hS
  have hb : r a b ∧ P b := by simpa [S] using hbS
  refine ⟨b, hb.1, hb.2, fun c hbc hPc => ?_⟩
  have hcS : c ∈ S := by simp [S, htrans hb.1 hbc, hPc]
  have hsub : up c ⊆ up b := by
    intro x hx
    simp only [up, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact htrans hbc hx
  have hle := hmin c hcS
  have heq : up c = up b := Finset.eq_of_subset_of_card_le hsub hle
  have : b ∈ up b := by simp [up, hrefl b]
  rw [← heq] at this
  simpa [up] using this
