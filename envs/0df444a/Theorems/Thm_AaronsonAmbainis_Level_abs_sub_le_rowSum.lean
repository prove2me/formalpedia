-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_abs_sub_le_rowSum
-- name    : AaronsonAmbainis.Level.abs_sub_le_rowSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:34:28.667643+00:00
-- url     : https://prove2.me/theorems/1798f5f1-1181-403b-90b3-ff5ccd7cb63d
-- title:
--   Level: abs sub le row Sum
-- statement:
--   The cost of a row of `f` at `x` is at least `|f(x) - f(y)|`, for every `y`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Basic.lean#L134-L138
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Basic.lean#L134-L138

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem AaronsonAmbainis.Level.abs_sub_le_rowSum {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ} (ha : ∀ x j, 0 ≤ a x j)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) (x y : Cube ι) :
    |f x - f y| ≤ ∑ j, a x j := by sorry
