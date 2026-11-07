-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_integrated_four_mul
-- name    : AaronsonAmbainis.Level.integrated_four_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:36:15.109674+00:00
-- url     : https://prove2.me/theorems/3065a4de-8a06-4f98-b400-d577bb0e6d8f
-- title:
--   Level: integrated four mul
-- statement:
--   The integrated all-pairs inequality, multiplied by `4`: for a real function `f` on the cube,
--   rows `a x` of `f` and weights `w > 0`,
--   `4 ∑_{(x,y) : f y < f x} (f x - f y)^3 / (6 ∑_{j ∈ Δ(x,y)} w_j a^x_j a^y_j) ≤ 4^n ∑_j L_j / w_j`,
--   where `L_j = meanAbsIncr f j = E_x |f x - f (x^j)|`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Integrated.lean#L116-L154
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Integrated.lean#L116-L154

import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Level_Integral
import Definitions.Def_AaronsonAmbainis_Level_AllPairs
import Definitions.Def_AaronsonAmbainis_Level_Integrated
set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Level
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Level.integrated_four_mul (hAllPairs : AllPairsInequality) (f : Cube ι → ℝ)
    (a : Cube ι → ι → ℝ) (ha : ∀ x j, 0 ≤ a x j)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) (w : ι → ℝ) (hw : ∀ j, 0 < w j) :
    4 * ∑ x, ∑ y ∈ univ.filter (fun y => f y < f x),
        (f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j)
      ≤ 4 ^ Fintype.card ι * ∑ j, meanAbsIncr f j / w j := by sorry
