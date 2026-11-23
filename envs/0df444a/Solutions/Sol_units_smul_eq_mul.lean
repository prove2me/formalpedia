-- Prove2me | solution 1 for units_smul_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:17:51.759958+00:00
-- url     : https://prove2.me/submissions/f3ba9f90-e709-485f-a630-f584377255a5

import Mathlib
import Definitions.Def_SimpleRbrFri_Core

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] (a x : Fˣ) : a • x = a * x :=
  Units.smul_eq_mul ..
