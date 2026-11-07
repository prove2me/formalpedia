-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_cost_pos
-- name    : AaronsonAmbainis.Level.cost_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:38:40.804789+00:00
-- url     : https://prove2.me/theorems/4f2e5f20-7f76-4aec-8656-2e929825c084
-- title:
--   Level: cost pos
-- statement:
--   If `f` has a row of cost at most `K` at every point and `Var(f) > 0`, then `K > 0`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Basic.lean#L148-L157
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Basic.lean#L148-L157

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Level.cost_pos {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ} {K : ℝ} (ha : ∀ x j, 0 ≤ a x j)
    (hsum : ∀ x, ∑ j, a x j ≤ K) (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j)
    (hvar : 0 < variance f) : 0 < K := by sorry
