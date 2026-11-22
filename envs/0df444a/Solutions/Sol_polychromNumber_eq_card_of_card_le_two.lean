-- Prove2me | solution 1 for polychromNumber_eq_card_of_card_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:46:12.474579+00:00
-- url     : https://prove2.me/submissions/cd1d303a-a56e-4790-b874-d1c755607918

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Theorems.Thm_polychromNumber_singleton
import Theorems.Thm_polychromNumber_eq_card_of_subsingleton
import Theorems.Thm_polychromNumber_univ
import Theorems.Thm_polychromNumber_pair
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ


attribute [local simp] polychromNumber_singleton
attribute [local simp] polychromNumber_univ
attribute [local simp] polychromNumber_pair

set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise
theorem _root_.solution [IsAddTorsionFree G] {S : Finset G} (hS : #S ≤ 2) :
    polychromNumber S = #S := by
  obtain hS2 | hS2 := lt_or_eq_of_le hS
  · rw [Nat.lt_succ_iff, Finset.card_le_one_iff_subsingleton] at hS2
    apply polychromNumber_eq_card_of_subsingleton hS2
  · classical
    rw [Finset.card_eq_two] at hS2
    obtain ⟨x, y, hxy, rfl⟩ := hS2
    simp [hxy]
