-- Prove2me | solution 1 for straussFunction_le_of_forall_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:44:30.451823+00:00
-- url     : https://prove2.me/submissions/d176738c-986b-43eb-b01e-d6cf0deb2e75

import Definitions.Def_Polychromatic_Existence
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_LovaszFunction
import Theorems.Thm_straussFunction_le_of_forall
import Theorems.Thm_HasPolychromColouring_subset
import Theorems.Thm_IsPolychrom_subset


set_option autoImplicit true
open Finset
theorem _root_.solution {k m : ℕ}
    (h : ∀ S : Finset ℤ, #S = m → HasPolychromColouring (Fin k) S) :
    straussFunction k ≤ m := by
  apply straussFunction_le_of_forall
  intro S hS
  obtain ⟨S', hS', hS'eq⟩ := exists_subset_card_eq hS
  exact (h S' hS'eq).subset hS'
