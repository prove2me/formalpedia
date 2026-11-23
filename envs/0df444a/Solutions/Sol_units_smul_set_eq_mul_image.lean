-- Prove2me | solution 1 for units_smul_set_eq_mul_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:20:15.46281+00:00
-- url     : https://prove2.me/submissions/055d6f9f-5d43-4aa8-8874-b103512f76d4

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
import Theorems.Thm_units_smul_eq_mul

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] (H : Subgroup Fˣ) (a : Fˣ) :
    a • (H : Set Fˣ) = Set.image (fun x ↦ a * x) (H : Set Fˣ) := by
  ext x; grind only [Set.mem_smul_set, SetLike.mem_coe, Set.mem_image, units_smul_eq_mul]
