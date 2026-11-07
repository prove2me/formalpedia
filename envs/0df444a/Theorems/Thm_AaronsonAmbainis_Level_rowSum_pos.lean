-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_rowSum_pos
-- name    : AaronsonAmbainis.Level.rowSum_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:34:55.733925+00:00
-- url     : https://prove2.me/theorems/6ffcd60c-4c2f-4207-86cd-c5e9e244dd94
-- title:
--   Level: row Sum pos
-- statement:
--   A row at `x` has positive cost if `f` takes another value somewhere.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Basic.lean#L142-L145
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Basic.lean#L142-L145

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem AaronsonAmbainis.Level.rowSum_pos {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ} (ha : ∀ x j, 0 ≤ a x j)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) {x y : Cube ι} (hxy : f x ≠ f y) :
    0 < ∑ j, a x j := by sorry
