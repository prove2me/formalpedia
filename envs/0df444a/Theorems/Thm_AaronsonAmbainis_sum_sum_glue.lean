-- Prove2me | Theorems.Thm_AaronsonAmbainis_sum_sum_glue
-- name    : AaronsonAmbainis.sum_sum_glue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:28:26.278076+00:00
-- url     : https://prove2.me/theorems/c0686491-9428-4b4e-ad16-046f7cf04d62
-- title:
--   Aaronson Ambainis: sum sum glue
-- statement:
--   Every point `x` is `glue F z u` for exactly `2 ^ n` pairs `(z, u)`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Glue.lean#L62-L77
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Glue.lean#L62-L77

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_TwoSided_Glue
set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.sum_sum_glue (F : Finset ι) (φ : Cube ι → ℝ) :
    ∑ z, ∑ u, φ (glue F z u) = 2 ^ Fintype.card ι * ∑ x, φ x := by sorry
