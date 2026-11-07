-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_sum_levRow
-- name    : AaronsonAmbainis.Level.sum_levRow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:33:59.397881+00:00
-- url     : https://prove2.me/theorems/7fead698-caf1-4595-ad0d-e96030be7d87
-- title:
--   Level: sum lev Row
-- statement:
--   The overlap sum of the level rows at a point above the level and a point below it
--   (Lemma 7.1 (i) of the paper).
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/AllPairs.lean#L30-L48
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/AllPairs.lean#L30-L48

import Definitions.Def_AaronsonAmbainis_Level_Rows
import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Level_AllPairs
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem AaronsonAmbainis.Level.sum_levRow (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ) (w : ι → ℝ) {t : ℝ} {x y : Cube ι}
    (hx : t < f x) (hy : f y < t) :
    ∑ j ∈ diffSet x y, w j * levRow f a t x j * levRow f a t y j
      = (∑ j ∈ diffSet x y, w j * a x j * a y j) / ((f x - t) * (t - f y)) := by sorry
