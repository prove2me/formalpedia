-- Prove2me | solution 1 for exists_maximal_element_finite__p2m_8824e35c_b427_4577_adf2_2966f46879ec_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:42:11.923965+00:00
-- url     : https://prove2.me/submissions/3c73abea-2361-48dd-98d7-4cb3eaa10e1d

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} [Fintype α] [PartialOrder α] (p : α → Prop)
    (hne : ∃ a, p a) :
    ∃ a, p a ∧ ∀ b, p b → a ≤ b → b = a := by
  classical
  let s : Set α := {a | p a}
  have hs : s.Finite := Set.toFinite s
  have hsn : s.Nonempty := by
    rcases hne with ⟨a, ha⟩
    exact ⟨a, ha⟩
  obtain ⟨a, ha, hmax⟩ := hs.exists_maximal hsn
  have hpa : p a := by
    simpa [s] using ha
  refine ⟨a, hpa, ?_⟩
  intro b hpb hab
  have hbs : b ∈ s := by
    simpa [s] using hpb
  exact le_antisymm (hmax hbs hab) hab