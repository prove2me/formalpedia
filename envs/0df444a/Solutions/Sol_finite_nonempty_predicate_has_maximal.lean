-- Prove2me | solution 1 for finite_nonempty_predicate_has_maximal
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:31:39.597724+00:00
-- url     : https://prove2.me/submissions/c153d580-0290-4cd9-926f-128dc10450f4

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} [Fintype α] [PartialOrder α]
    (P : α → Prop) [DecidablePred P]
    (hP : ∃ x, P x) :
    ∃ x, P x ∧ ∀ y, P y → x ≤ y → y ≤ x := by
  classical
  obtain ⟨a, ha⟩ := hP
  obtain ⟨x, hx⟩ :=
    WellFoundedGT.exists_maximal (inferInstance : WellFoundedGT α)
      {x | P x} ⟨a, ha⟩
  exact ⟨x, hx.1, hx.2⟩