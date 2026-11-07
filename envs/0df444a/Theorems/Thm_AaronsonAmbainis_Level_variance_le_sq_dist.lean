-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_variance_le_sq_dist
-- name    : AaronsonAmbainis.Level.variance_le_sq_dist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:37:07.819071+00:00
-- url     : https://prove2.me/theorems/be0f3b81-0aa3-4b5f-a274-1c584c1386b9
-- title:
--   Level: variance le sq dist
-- statement:
--   The mean minimises the mean square distance to a constant.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Basic.lean#L82-L95
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Basic.lean#L82-L95

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Level.variance_le_sq_dist (f : Cube ι → ℝ) (c : ℝ) :
    variance f ≤ (∑ x, (f x - c) ^ 2) / 2 ^ Fintype.card ι := by sorry
