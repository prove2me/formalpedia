-- Prove2me | solution 1 for polychromNumber_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:43:43.099781+00:00
-- url     : https://prove2.me/submissions/452a3319-cd41-4259-8259-3e73931cd932

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Theorems.Thm_polychromNumber_singleton
import Theorems.Thm_polychromNumber_univ
import Theorems.Thm_polychromNumber_image
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
    {F : Type*} [EquivLike F G H] [AddEquivClass F G H] (φ : F)
    {S : Finset G} :
    polychromNumber (S.image φ) = polychromNumber S :=
  le_antisymm (polychromNumber_image φ) <| by
    classical
    have : polychromNumber ((S.image φ).image (φ : G ≃ H).symm) ≤ polychromNumber (S.image φ) :=
      polychromNumber_image (φ : G ≃+ H).symm
    simpa [Finset.image_image] using this
