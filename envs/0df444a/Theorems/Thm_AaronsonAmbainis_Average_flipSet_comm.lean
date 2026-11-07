-- Prove2me | Theorems.Thm_AaronsonAmbainis_Average_flipSet_comm
-- name    : AaronsonAmbainis.Average.flipSet_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:35:53.111227+00:00
-- url     : https://prove2.me/theorems/9a549d0e-af27-425f-99f3-db820a415345
-- title:
--   Average: flip Set comm
-- statement:
--   Flips commute.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Average/Coordinate.lean#L30-L33
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Average/Coordinate.lean#L30-L33

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Average_Coordinate
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Average
open Finset
variable {ι : Type*} [DecidableEq ι]

theorem AaronsonAmbainis.Average.flipSet_comm (x : Cube ι) (S T : Finset ι) :
    flipSet (flipSet x S) T = flipSet (flipSet x T) S := by sorry
