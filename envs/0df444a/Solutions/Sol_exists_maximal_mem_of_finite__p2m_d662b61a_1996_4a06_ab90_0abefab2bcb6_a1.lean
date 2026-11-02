-- Prove2me | solution 1 for exists_maximal_mem_of_finite__p2m_d662b61a_1996_4a06_ab90_0abefab2bcb6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:36:57.322577+00:00
-- url     : https://prove2.me/submissions/8fb243b4-d989-4f75-adda-b0135342cfeb

import Mathlib

set_option autoImplicit false

theorem solution {α : Type} [Finite α] [PartialOrder α] (S : Set α)
    (hS : S.Nonempty) : ∃ a ∈ S, ∀ b ∈ S, a ≤ b → b = a := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  have hfin : ∀ t : Finset α, t.Nonempty →
      ∃ a ∈ t, ∀ b ∈ t, a ≤ b → b = a := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        intro ht
        simp at ht
    | @insert x t hxt ih =>
        intro ht
        by_cases htn : t.Nonempty
        · obtain ⟨a, ha, hmax⟩ := ih htn
          by_cases hax : a ≤ x
          · refine ⟨x, Finset.mem_insert_self x t, ?_⟩
            intro b hb hxb
            rcases Finset.mem_insert.mp hb with rfl | hb
            · rfl
            · have hab : a ≤ b := le_trans hax hxb
              have hba : b = a := hmax b hb hab
              subst b
              exact le_antisymm hax hxb
          · refine ⟨a, Finset.mem_insert_of_mem ha, ?_⟩
            intro b hb hab
            rcases Finset.mem_insert.mp hb with rfl | hb
            · exact (hax hab).elim
            · exact hmax b hb hab
        · refine ⟨x, Finset.mem_insert_self x t, ?_⟩
          intro b hb _
          rcases Finset.mem_insert.mp hb with rfl | hb
          · rfl
          · exact (htn ⟨b, hb⟩).elim
  let t : Finset α := Finset.univ.filter (fun x => x ∈ S)
  obtain ⟨a, ha, hmax⟩ := hfin t ⟨Classical.choose hS, by
    simp [t, Classical.choose_spec hS]
  ⟩
  refine ⟨a, ?_, ?_⟩
  · simpa [t] using (Finset.mem_filter.mp ha).2
  · intro b hb hab
    apply hmax b
    · simp [t, hb]
    · exact hab