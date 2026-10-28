-- Prove2me | solution 1 for finite_predicate_has_maximal_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:22:42.36093+00:00
-- url     : https://prove2.me/submissions/1ff6c618-c336-49c6-a399-f51a8dcd2c1e

import Mathlib

set_option autoImplicit false
theorem solution
    {α : Type} [Fintype α]
    (r : α → α → Prop)
    (hrefl : ∀ a, r a a)
    (htrans : ∀ a b c, r a b → r b c → r a c)
    (P : α → Prop)
    (a : α) (ha : P a) :
    ∃ b, P b ∧ r a b ∧ ∀ c, P c → r b c → r c b := by
  classical
  let S : Finset α := Finset.univ.filter (fun b => P b ∧ r a b)
  have hS : S.Nonempty := ⟨a, by simp [S, ha, hrefl a]⟩
  let f : α → ℕ := fun b => (Finset.univ.filter (fun x => r x b)).card
  obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image S f hS
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hb hmax
  refine ⟨b, hb.1, hb.2, fun c hc hbc => ?_⟩
  by_contra hcb
  have hle := hmax c ⟨hc, htrans a b c hb.2 hbc⟩
  have hsub : Finset.univ.filter (fun x => r x b) ⊂ Finset.univ.filter (fun x => r x c) := by
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨c, by simp [hrefl c], by simp [hcb]⟩
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact htrans x b c hx hbc
  exact absurd (Finset.card_lt_card hsub) (not_lt.mpr hle)
