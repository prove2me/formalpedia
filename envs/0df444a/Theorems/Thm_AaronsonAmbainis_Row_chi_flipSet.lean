-- Prove2me | Theorems.Thm_AaronsonAmbainis_Row_chi_flipSet
-- name    : AaronsonAmbainis.Row.chi_flipSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:03:24.990746+00:00
-- url     : https://prove2.me/theorems/1da6c03f-f23d-44f6-88a4-fa075b2b7df6
-- title:
--   Row: chi flip Set
-- statement:
--   The character at a flipped point.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Chi.lean#L55-L58
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Chi.lean#L55-L58

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Row_Chi
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset
variable {ι : Type*}

theorem AaronsonAmbainis.Row.chi_flipSet [DecidableEq ι] (T U : Finset ι) (x : Cube ι) :
    chi T (flipSet x U) = ∏ i ∈ T, (sgn (x i) * (if i ∈ U then -1 else 1)) := by sorry
