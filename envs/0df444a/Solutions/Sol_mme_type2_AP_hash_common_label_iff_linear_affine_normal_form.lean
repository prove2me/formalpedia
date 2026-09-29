-- Prove2me | solution 1 for mme_type2_AP_hash_common_label_iff_linear_affine_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:11:34.43887+00:00
-- url     : https://prove2.me/submissions/c406042e-02ea-4741-a17c-7917f6eb7d95

import Mathlib

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {R Label : Type*} [CommRing R] [DecidableEq R] [DecidableEq Label]
    (S : Finset Label) (label : Label → R) (H : Fin 3 → R)
    (hAP : H 0 + H 1 = 2 * H 2) :
    (∃ s ∈ S, ∀ i : Fin 3, H i = label s) ↔
      H 0 ∈ S.image label ∧ H 2 = H 0 := by
  constructor
  · rintro ⟨s, hs, hcommon⟩
    refine ⟨Finset.mem_image.mpr ⟨s, hs, (hcommon 0).symm⟩, ?_⟩
    exact (hcommon 2).trans (hcommon 0).symm
  · rintro ⟨hlabel, h20⟩
    obtain ⟨s, hs, hs0⟩ := Finset.mem_image.mp hlabel
    have h1 : H 1 = H 0 := by
      rw [h20] at hAP
      linear_combination hAP
    refine ⟨s, hs, ?_⟩
    intro i
    fin_cases i
    · exact hs0.symm
    · exact h1.trans hs0.symm
    · exact h20.trans hs0.symm
