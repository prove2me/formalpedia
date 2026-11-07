-- Prove2me | Theorems.Thm_AaronsonAmbainis_Average_diffSet_flip
-- name    : AaronsonAmbainis.Average.diffSet_flip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:37:09.594769+00:00
-- url     : https://prove2.me/theorems/5a3d9ba0-614f-4fb2-a2a8-3685df08c7a7
-- title:
--   Average: diff Set flip
-- statement:
--   Flipping the same coordinates in two points does not change the set where they differ.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Average/Coordinate.lean#L40-L47
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Average/Coordinate.lean#L40-L47

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Average_Coordinate
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Average
open Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Average.diffSet_flip (x y : Cube ι) (S : Finset ι) :
    diffSet (flipSet x S) (flipSet y S) = diffSet x y := by sorry
