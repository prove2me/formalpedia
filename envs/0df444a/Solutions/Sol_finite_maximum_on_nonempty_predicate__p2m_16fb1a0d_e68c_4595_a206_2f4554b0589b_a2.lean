-- Prove2me | solution 1 for finite_maximum_on_nonempty_predicate__p2m_16fb1a0d_e68c_4595_a206_2f4554b0589b_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:40:38.617775+00:00
-- url     : https://prove2.me/submissions/9cdde432-b01b-4700-b729-eaf5ca65060f

import Mathlib

theorem solution
    {α : Type} [Fintype α] (P : α → Prop) (f : α → Nat)
    (hP : ∃ x, P x) :
    ∃ x, P x ∧ ∀ y, P y → f y ≤ f x := by
  classical
  let s : Finset α := Finset.univ.filter P
  have hs : s.Nonempty := by
    rcases hP with ⟨x, hx⟩
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
  obtain ⟨x, hx, hxmax⟩ := Finset.exists_max_image s f hs
  refine ⟨x, (Finset.mem_filter.mp hx).2, ?_⟩
  intro y hy
  exact hxmax y (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩)