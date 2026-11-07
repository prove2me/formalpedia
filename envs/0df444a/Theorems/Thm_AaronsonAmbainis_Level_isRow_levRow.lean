-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_isRow_levRow
-- name    : AaronsonAmbainis.Level.isRow_levRow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:32:44.224757+00:00
-- url     : https://prove2.me/theorems/23f55a50-be08-496f-acb3-b16056bf88fc
-- title:
--   Level: is Row lev Row
-- statement:
--   `levRow f a t x` is a row of `g_t` at `x`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Rows.lean#L43-L68
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Rows.lean#L43-L68

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Rows
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Level.isRow_levRow {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ} (ha : ∀ x j, 0 ≤ a x j)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) (t : ℝ) (x : Cube ι) :
    IsRow (lev f t) x (levRow f a t x) := by sorry
