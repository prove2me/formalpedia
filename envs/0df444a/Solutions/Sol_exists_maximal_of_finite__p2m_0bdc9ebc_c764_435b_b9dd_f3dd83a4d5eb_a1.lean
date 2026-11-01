-- Prove2me | solution 1 for exists_maximal_of_finite__p2m_0bdc9ebc_c764_435b_b9dd_f3dd83a4d5eb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:26:04.110204+00:00
-- url     : https://prove2.me/submissions/eba21545-4aa1-4d26-ba4f-5414340c8121

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} [Finite α] [PartialOrder α]
    (P : α → Prop) (a₀ : α) (ha₀ : P a₀) :
    ∃ a, P a ∧ ∀ b, a ≤ b → P b → b = a := by
  classical
  obtain ⟨a, ha, hmax⟩ :=
    (Set.toFinite {x : α | P x}).exists_maximal ⟨a₀, ha₀⟩
  refine ⟨a, ha, ?_⟩
  intro b hab hb
  exact le_antisymm (hmax hb hab) hab