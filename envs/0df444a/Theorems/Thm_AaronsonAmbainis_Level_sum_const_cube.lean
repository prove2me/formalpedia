-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_sum_const_cube
-- name    : AaronsonAmbainis.Level.sum_const_cube
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:34:14.009539+00:00
-- url     : https://prove2.me/theorems/d5a7cf0e-62eb-44b4-b6a5-767e044fe12b
-- title:
--   Level: sum const cube
-- statement:
--   Sum of a constant over the cube.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Basic.lean#L43-L44
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Basic.lean#L43-L44

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Level.sum_const_cube (c : ℝ) : ∑ _x : Cube ι, c = 2 ^ Fintype.card ι * c := by sorry
