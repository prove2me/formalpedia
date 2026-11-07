-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_abs_sub_le_of_lev_ne
-- name    : AaronsonAmbainis.Level.abs_sub_le_of_lev_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:32:09.046417+00:00
-- url     : https://prove2.me/theorems/ddb6396b-966c-42f5-88e6-776b5188690f
-- title:
--   Level: abs sub le of lev ne
-- statement:
--   If `g_t` separates `x` and `y` then `t` lies weakly between `f x` and `f y`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Rows.lean#L29-L38
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Rows.lean#L29-L38

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Rows
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset

theorem AaronsonAmbainis.Level.abs_sub_le_of_lev_ne {ι : Type*} {f : Cube ι → ℝ} {t : ℝ} {x y : Cube ι}
    (h : lev f t y ≠ lev f t x) : |f x - t| ≤ |f x - f y| := by sorry
