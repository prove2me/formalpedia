-- Prove2me | solution 1 for finite_set_exists_maximal__p2m_0d714fcf_7da8_48c8_afc4_fedf819778b0_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:14:54.464914+00:00
-- url     : https://prove2.me/submissions/73a73ace-3685-4861-b391-1d5e728ce581

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} [Preorder α] [Finite α]
    (s : Set α) (hs : s.Finite) (hne : s.Nonempty) :
    ∃ a ∈ s, ∀ b ∈ s, a ≤ b → b ≤ a := by
  classical
  let u : Finset α := hs.toFinset
  have hneU : u.Nonempty := by
    rcases hne with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    change a ∈ hs.toFinset
    exact hs.mem_toFinset.mpr ha
  have aux :
      ∀ t : Finset α, t.Nonempty →
        ∃ a ∈ t, ∀ b ∈ t, a ≤ b → b ≤ a := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        intro ht
        rcases ht with ⟨a, ha⟩
        have : False := by simpa using ha
        exact this.elim
    | @insert x t hx ih =>
        intro ht
        by_cases htn : t.Nonempty
        · obtain ⟨a, ha, hmax⟩ := ih htn
          by_cases hax : a ≤ x
          · refine ⟨x, Finset.mem_insert_self x t, ?_⟩
            intro b hb hxb
            rcases Finset.mem_insert.mp hb with rfl | hb
            · exact le_rfl
            · exact le_trans (hmax b hb (le_trans hax hxb)) hax
          · refine ⟨a, Finset.mem_insert_of_mem ha, ?_⟩
            intro b hb hab
            rcases Finset.mem_insert.mp hb with rfl | hb
            · exact False.elim (hax hab)
            · exact hmax b hb hab
        · refine ⟨x, Finset.mem_insert_self x t, ?_⟩
          intro b hb hxb
          rcases Finset.mem_insert.mp hb with rfl | hb
          · exact le_rfl
          · exact False.elim (htn ⟨b, hb⟩)
  obtain ⟨a, ha, hmax⟩ := aux u hneU
  refine ⟨a, ?_, ?_⟩
  · change a ∈ hs.toFinset at ha
    exact hs.mem_toFinset.mp ha
  · intro b hb hab
    apply hmax b
    · change b ∈ hs.toFinset
      exact hs.mem_toFinset.mpr hb
    · exact hab