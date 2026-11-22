-- Prove2me | solution 1 for polychromNumber_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:43:03.019541+00:00
-- url     : https://prove2.me/submissions/af9c6cb5-9b95-4588-b688-79557f0a5a49

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Theorems.Thm_le_polychromNumber
import Theorems.Thm_polychromNumber_singleton
import Theorems.Thm_polychromNumber_univ
import Theorems.Thm_HasPolychromColouring_of_image
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ


attribute [local simp] polychromNumber_singleton
attribute [local simp] polychromNumber_univ

set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise
theorem _root_.solution {H : Type*} [DecidableEq H] [AddCommGroup H]
    {F : Type*} [FunLike F G H] [AddHomClass F G H] (φ : F) {S : Finset G} :
    polychromNumber (S.image φ) ≤ polychromNumber S := by
  obtain rfl | hS' := S.eq_empty_or_nonempty
  · simp
  exact le_polychromNumber (.of_image _ (hasPolychromColouring_fin (hS'.image φ)))
