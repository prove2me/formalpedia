-- Prove2me | solution 1 for exists_maximal_of_nonempty_finset__p2m_5ce86dee_a51b_43d9_9c16_6a53f5f31031_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:43:29.947003+00:00
-- url     : https://prove2.me/submissions/0562e36e-7bd3-45d9-b93e-678e2c434360

import Mathlib
set_option autoImplicit false

theorem solution
    {alpha : Type} [PartialOrder alpha] (s : Finset alpha) (hs : s.Nonempty) :
    ∃ x ∈ s, ∀ y ∈ s, x ≤ y → y ≤ x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp at hs
  | @insert a s ha ih =>
      by_cases hs' : s.Nonempty
      · obtain ⟨x, hxmem, hxmax⟩ := ih hs'
        by_cases hxa : x ≤ a
        · refine ⟨a, Finset.mem_insert_self a s, ?_⟩
          intro y hym hy
          rcases Finset.mem_insert.mp hym with rfl | hys
          · exact hy
          · have hxy : x ≤ y := le_trans hxa hy
            exact le_trans (hxmax y hys hxy) hxa
        · refine ⟨x, Finset.mem_insert_of_mem hxmem, ?_⟩
          intro y hym hxy
          rcases Finset.mem_insert.mp hym with rfl | hys
          · exact (hxa hxy).elim
          · exact hxmax y hys hxy
      · have hsEq : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
        subst s
        refine ⟨a, by simp, ?_⟩
        intro y hym hy
        rcases Finset.mem_insert.mp hym with rfl | hfalse
        · exact hy
        · simp at hfalse