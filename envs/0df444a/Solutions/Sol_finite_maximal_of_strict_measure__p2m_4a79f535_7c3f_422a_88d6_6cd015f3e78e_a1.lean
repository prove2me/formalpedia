-- Prove2me | solution 1 for finite_maximal_of_strict_measure__p2m_4a79f535_7c3f_422a_88d6_6cd015f3e78e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:03:04.746806+00:00
-- url     : https://prove2.me/submissions/8abe6120-4aa8-4ffe-b026-1ff0126f4ba3

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} [Fintype α] [PartialOrder α]
    (Q : α → Prop) (measure : α → Nat)
    (hstrict : ∀ a b, a ≤ b → a ≠ b → measure a < measure b)
    (hne : ∃ a, Q a) :
    ∃ a, Q a ∧ ∀ b, Q b → a ≤ b → b = a := by
  classical
  let s : Finset α := Finset.univ.filter Q
  have hs : s.Nonempty := by
    rcases hne with ⟨a, ha⟩
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩
  let values : Finset Nat := s.image measure
  have hvalues : values.Nonempty := by
    rcases hs with ⟨a, ha⟩
    exact ⟨measure a, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩
  let m : Nat := values.max' hvalues
  have hm : m ∈ values := by
    exact Finset.max'_mem values hvalues
  rcases Finset.mem_image.mp hm with ⟨a, ha, hmeasure⟩
  refine ⟨a, (Finset.mem_filter.mp ha).2, ?_⟩
  intro b hb hab
  by_contra hne
  have hlt : measure a < measure b := hstrict a b hab (Ne.symm hne)
  have hbmem : measure b ∈ values := by
    exact Finset.mem_image.mpr
      ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, rfl⟩
  have hbmax : measure b ≤ m := by
    simpa [m] using Finset.le_max' values (measure b) hbmem
  rw [← hmeasure] at hbmax
  omega
