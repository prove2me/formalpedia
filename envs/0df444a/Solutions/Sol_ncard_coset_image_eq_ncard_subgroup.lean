-- Prove2me | solution 1 for ncard_coset_image_eq_ncard_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:17:47.495154+00:00
-- url     : https://prove2.me/submissions/dbf614b9-6f89-4a9d-9edb-081c9be60a46

import Mathlib
import Definitions.Def_SimpleRbrFri_Core

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F]
    (H : Subgroup Fˣ) (a : Fˣ) :
    (Set.image (fun x : Fˣ ↦ (x : F)) (a • (H : Set Fˣ))).ncard = (H : Set Fˣ).ncard := by
  rw [Set.ncard_image_of_injective _ Units.val_injective, Set.ncard_smul_set]
