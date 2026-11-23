-- Prove2me | solution 1 for subgroup_finite_of_coset_image_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:00:19.703432+00:00
-- url     : https://prove2.me/submissions/a29506be-f022-4e0c-b5bb-e18ada41c766

import Mathlib
import Definitions.Def_SimpleRbrFri_Core

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F]
    (H : Subgroup Fˣ) (a : Fˣ)
    (h_finite : Set.Finite (Set.image (fun x : Fˣ ↦ (x : F)) (a • (H : Set Fˣ)))) :
    Set.Finite (H : Set Fˣ) :=
  Set.finite_smul_set.mp <| h_finite.of_finite_image Units.val_injective.injOn
