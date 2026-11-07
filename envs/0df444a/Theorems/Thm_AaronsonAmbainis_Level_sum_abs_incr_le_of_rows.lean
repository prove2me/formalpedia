-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_sum_abs_incr_le_of_rows
-- name    : AaronsonAmbainis.Level.sum_abs_incr_le_of_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:35:06.413013+00:00
-- url     : https://prove2.me/theorems/b570debb-789d-43cb-aa75-83cb6cb46a9f
-- title:
--   Level: sum abs incr le of rows
-- statement:
--   A row at `u` of cost at most `K` bounds the sum of the increments of `f` at `u`:
--   `∑_j |f(u) - f(u^j)| ≤ K`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Basic.lean#L168-L171
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Basic.lean#L168-L171

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Level.sum_abs_incr_le_of_rows {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ} {K : ℝ}
    (hsum : ∀ x, ∑ j, a x j ≤ K) (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j)
    (u : Cube ι) : ∑ j, |f u - f (flipSet u {j})| ≤ K := by sorry
