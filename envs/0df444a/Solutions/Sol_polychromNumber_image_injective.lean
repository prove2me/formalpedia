-- Prove2me | solution 1 for polychromNumber_image_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:44:29.998231+00:00
-- url     : https://prove2.me/submissions/4307af14-a2d1-4449-800b-14940e3250ad

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Theorems.Thm_polychromNumber_iso
import Theorems.Thm_polychromNumber_subgroup

set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise
theorem _root_.solution {H : Type*} [DecidableEq H] [AddCommGroup H]
    {F : Type*} [FunLike F G H] [AddMonoidHomClass F G H] (φ : F) (hφ : Function.Injective φ)
    {S : Finset G} :
    polychromNumber (S.image φ) = polychromNumber S := by
  let ψ := AddMonoidHom.ofInjective (f := (φ : G →+ H)) hφ
  rw [← polychromNumber_iso ψ, polychromNumber_subgroup _, Finset.image_image]
  rfl
