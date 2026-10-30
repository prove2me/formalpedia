-- Prove2me | solution 1 for exists_maximal_of_finite_partialOrder__p2m_0e06c23e_290e_423e_a5fe_9ac4288d0e45_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:49:05.293428+00:00
-- url     : https://prove2.me/submissions/44698130-c7d7-4375-95f7-a32dbe7d397a

import Mathlib

set_option autoImplicit false

theorem solution {α : Type} [PartialOrder α] [Finite α] (P : α → Prop)
    (hP : ∃ a, P a) : ∃ a, P a ∧ ∀ b, a ≤ b → b ≠ a → ¬ P b := by
  classical
  let s : Set α := {a | P a}
  have hsFinite : s.Finite := Set.toFinite s
  have hsNonempty : s.Nonempty := by
    rcases hP with ⟨a, ha⟩
    exact ⟨a, ha⟩
  obtain ⟨a, haMax⟩ := hsFinite.exists_maximal hsNonempty
  rcases (maximal_iff_forall_gt).1 haMax with ⟨ha, hmax⟩
  change P a at ha
  refine ⟨a, ha, ?_⟩
  intro b hab hba hPb
  exact hmax (lt_of_le_of_ne hab (Ne.symm hba)) (by simpa [s] using hPb)