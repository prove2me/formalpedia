-- Prove2me | solution 1 for polychromNumber_eq_card_of_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:43:48.844267+00:00
-- url     : https://prove2.me/submissions/4a06488c-c02c-4152-ba40-501181e06429

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Theorems.Thm_polychromNumber_singleton
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ


attribute [local simp] polychromNumber_singleton

set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise
theorem _root_.solution (hS : (S : Set G).Subsingleton) :
    polychromNumber S = #S := by
  obtain rfl | ⟨x, hx⟩ := S.eq_empty_or_nonempty
  · simp
  rw [Set.subsingleton_iff_singleton (by simpa using hx)] at hS
  simp only [coe_eq_singleton] at hS
  simp [hS]
