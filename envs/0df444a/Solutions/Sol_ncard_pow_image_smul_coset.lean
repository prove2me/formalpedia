-- Prove2me | solution 1 for ncard_pow_image_smul_coset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:22:05.95575+00:00
-- url     : https://prove2.me/submissions/ad796117-9192-4734-9626-2e2958520033

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
import Theorems.Thm_ncard_pow_image_mul_coset
import Theorems.Thm_units_smul_set_eq_mul_image

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] (H : Subgroup Fˣ) (a : Fˣ) (m : ℕ) :
    (Set.image (fun x ↦ x ^ m) (a • (H : Set Fˣ))).ncard =
    (Set.image (fun x ↦ x ^ m) (H : Set Fˣ)).ncard :=
  units_smul_set_eq_mul_image H a ▸ ncard_pow_image_mul_coset H a m
