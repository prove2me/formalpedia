-- Prove2me | solution 1 for finite_finset_maximal_element__p2m_e3d00913_05dd_434d_bc2d_b9a3208fb1a4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:43:02.026966+00:00
-- url     : https://prove2.me/submissions/0da53255-534d-4bda-a661-f54dbc5dd7cc

import Mathlib

theorem solution {α : Type} [Fintype α] (P : Finset α → Prop) (s₀ : Finset α) (hs₀ : P s₀) :
    ∃ s, P s ∧ ∀ t, s ⊂ t → ¬ P t := by
  classical
  let F : Finset (Finset α) := Finset.univ.filter P
  have hF : F.Nonempty := by
    refine ⟨s₀, ?_⟩
    simp [F, hs₀]
  obtain ⟨s, hsF, hmax⟩ := Finset.exists_max_image F Finset.card hF
  refine ⟨s, (Finset.mem_filter.mp hsF).2, ?_⟩
  intro t hst ht
  have htF : t ∈ F := by
    simp [F, ht]
  have hcard : Finset.card t ≤ Finset.card s := hmax t htF
  have hstrict : Finset.card s < Finset.card t := Finset.card_lt_card hst
  omega