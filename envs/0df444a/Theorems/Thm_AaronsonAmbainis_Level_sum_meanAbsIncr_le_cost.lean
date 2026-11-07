-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_sum_meanAbsIncr_le_cost
-- name    : AaronsonAmbainis.Level.sum_meanAbsIncr_le_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:38:56.562148+00:00
-- url     : https://prove2.me/theorems/3d0405ef-c8cc-4d36-aace-f5c5dc1645f0
-- title:
--   Level: sum mean Abs Incr le cost
-- statement:
--   The sum `L(f)` of the mean absolute increments of a function with rows of cost at most `K`
--   is at most `K`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Basic.lean#L186-L189
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Basic.lean#L186-L189

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Level.sum_meanAbsIncr_le_cost {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ} {K : ℝ}
    (hsum : ∀ x, ∑ j, a x j ≤ K) (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) :
    ∑ j, meanAbsIncr f j ≤ K := by sorry
