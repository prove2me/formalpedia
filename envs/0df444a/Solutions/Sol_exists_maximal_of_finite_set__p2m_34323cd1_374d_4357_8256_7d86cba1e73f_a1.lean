-- Prove2me | solution 1 for exists_maximal_of_finite_set__p2m_34323cd1_374d_4357_8256_7d86cba1e73f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:10:20.131+00:00
-- url     : https://prove2.me/submissions/b09307d8-936d-451e-83f9-ec1860047845

import Mathlib

set_option autoImplicit false

theorem solution {α : Type} [PartialOrder α] (S : Set α) (hS : S.Finite)
    (hSne : S.Nonempty) : ∃ a ∈ S, ∀ b ∈ S, a ≤ b → b = a := by
  classical
  obtain ⟨a, ha⟩ := hS.exists_maximal hSne
  refine ⟨a, ha.1, ?_⟩
  intro b hb hab
  exact le_antisymm (ha.2 hb hab) hab