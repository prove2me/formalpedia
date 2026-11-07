-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_abs_incr_le_of_rows
-- name    : AaronsonAmbainis.Level.abs_incr_le_of_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:34:48.917428+00:00
-- url     : https://prove2.me/theorems/820def2f-f4d0-444f-afa5-280de0afdc6a
-- title:
--   Level: abs incr le of rows
-- statement:
--   A row at `u` bounds each increment of `f` at `u`: `|f(u) - f(u^j)| ≤ a u j`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Basic.lean#L160-L164
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Basic.lean#L160-L164

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Level.abs_incr_le_of_rows {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ}
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) (u : Cube ι) (j : ι) :
    |f u - f (flipSet u {j})| ≤ a u j := by sorry
