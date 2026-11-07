-- Prove2me | Theorems.Thm_AaronsonAmbainis_Row_sgn_flipSet
-- name    : AaronsonAmbainis.Row.sgn_flipSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:57:50.695022+00:00
-- url     : https://prove2.me/theorems/10969058-916e-4b9d-a479-4897c98c27ff
-- title:
--   Row: sgn flip Set
-- statement:
--   The sign of a coordinate of a flipped point.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Chi.lean#L50-L52
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Chi.lean#L50-L52

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Row_Chi
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset
variable {ι : Type*}

theorem AaronsonAmbainis.Row.sgn_flipSet [DecidableEq ι] (x : Cube ι) (U : Finset ι) (i : ι) :
    sgn (flipSet x U i) = sgn (x i) * (if i ∈ U then -1 else 1) := by sorry
