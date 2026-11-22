-- Prove2me | solution 1 for polychromNumber_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:43:48.370338+00:00
-- url     : https://prove2.me/submissions/aa835d0b-ae17-4d4d-beaa-025387d9918d

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Theorems.Thm_le_polychromNumber
import Theorems.Thm_HasPolychromColouring_subset
import Theorems.Thm_IsPolychrom_subset
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ



set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise
theorem _root_.solution {S' : Finset G} (hS' : S' ⊆ S) :
    polychromNumber S' ≤ polychromNumber S := by
  obtain rfl | hS'' := S'.eq_empty_or_nonempty
  · simp
  exact le_polychromNumber ((hasPolychromColouring_fin hS'').subset hS')
