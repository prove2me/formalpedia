-- Prove2me | solution 1 for finite_exists_max_rank__p2m_9e5fb9d2_aa0e_41c4_9a80_cb078400c4e8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:00:17.233195+00:00
-- url     : https://prove2.me/submissions/159263f4-d28d-4c2d-aca6-4c9a414dbc60

import Mathlib

set_option autoImplicit false

theorem solution {α : Type} [Finite α] (P : α → Prop) (rank : α → Nat)
    (hex : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, P b → rank b ≤ rank a := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  let s : Finset α := Finset.univ.filter P
  have hs : s.Nonempty := by
    rcases hex with ⟨a, ha⟩
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
  let t : Finset Nat := s.image rank
  have ht : t.Nonempty := by
    rcases hs with ⟨a, ha⟩
    exact ⟨rank a, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩
  obtain ⟨a, ha, hmax⟩ := Finset.mem_image.mp (Finset.max'_mem t ht)
  refine ⟨a, (Finset.mem_filter.mp ha).2, ?_⟩
  intro b hb
  have hb_s : b ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩
  have hb_t : rank b ∈ t := Finset.mem_image.mpr ⟨b, hb_s, rfl⟩
  have hle : rank b ≤ t.max' ht := by
    simpa using (Finset.le_max' t (rank b) hb_t)
  simpa [hmax] using hle
