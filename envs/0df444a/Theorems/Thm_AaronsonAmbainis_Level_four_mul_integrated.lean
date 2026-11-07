-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_four_mul_integrated
-- name    : AaronsonAmbainis.Level.four_mul_integrated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:37:18.038925+00:00
-- url     : https://prove2.me/theorems/c5ae069a-a0b5-4e39-b4d8-47a749d01ecf
-- title:
--   Level: four mul integrated
-- statement:
--   The integrated all-pairs inequality multiplied by `4`, so that `4^n` appears in place of
--   `4^(n-1)` (for `n = 0` both sides are `0`).
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/ThirdMoment.lean#L40-L51
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/ThirdMoment.lean#L40-L51

import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Level_AllPairs
import Definitions.Def_AaronsonAmbainis_TwoSided_CauchySchwarz
import Definitions.Def_AaronsonAmbainis_Level_ThirdMoment
set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Level
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Level.four_mul_integrated (hInt : IntegratedAllPairsInequality) (f : Cube ι → ℝ)
    (a : Cube ι → ι → ℝ) (ha : ∀ x j, 0 ≤ a x j)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) (w : ι → ℝ) (hw : ∀ j, 0 < w j) :
    4 * ∑ x, ∑ y ∈ univ.filter (fun y : Cube ι => f y < f x),
        (f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j)
      ≤ 4 ^ Fintype.card ι * ∑ j, meanAbsIncr f j / w j := by sorry
