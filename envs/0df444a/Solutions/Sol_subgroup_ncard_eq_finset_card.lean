-- Prove2me | solution 1 for subgroup_ncard_eq_finset_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:20:11.415805+00:00
-- url     : https://prove2.me/submissions/7c282a11-1237-43b9-abdc-54e4b8e5b4e6

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
import Theorems.Thm_ncard_coset_image_eq_ncard_subgroup

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] [DecidableEq F]
    (D : Finset F) (H : Subgroup Fˣ) (a : Fˣ)
    (hD : (D : Set F) = (a • (H : Set Fˣ)).image (fun x : Fˣ ↦ (x : F))) :
    (H : Set Fˣ).ncard = D.card := by
  simp only [← ncard_coset_image_eq_ncard_subgroup H a, ← Set.ncard_coe_finset, hD]
