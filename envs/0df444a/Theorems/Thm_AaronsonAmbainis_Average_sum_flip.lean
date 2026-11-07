-- Prove2me | Theorems.Thm_AaronsonAmbainis_Average_sum_flip
-- name    : AaronsonAmbainis.Average.sum_flip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:35:28.538205+00:00
-- url     : https://prove2.me/theorems/4449e8d4-e14a-442e-b675-3c2736d211ed
-- title:
--   Average: sum flip
-- statement:
--   The flip of the coordinate `j` is a bijection of the cube.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Average/Coordinate.lean#L50-L53
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Average/Coordinate.lean#L50-L53

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Average_Coordinate
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Average
open Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Average.sum_flip (j : ι) (F : Cube ι → ℝ) : ∑ x, F (flipSet x {j}) = ∑ x, F x := by sorry
