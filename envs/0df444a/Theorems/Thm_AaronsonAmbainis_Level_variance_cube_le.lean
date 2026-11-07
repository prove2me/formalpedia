-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_variance_cube_le
-- name    : AaronsonAmbainis.Level.variance_cube_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:57:45.519922+00:00
-- url     : https://prove2.me/theorems/f9751cea-68e1-4f4d-b56e-237b0504846f
-- title:
--   Level: variance cube le
-- statement:
--   `Var(f)^3 ≤ 36 K^4 M²` when `f` has rows of cost at most `K` everywhere and `M ≥ 0` bounds
--   all the mean absolute increments `L_j = meanAbsIncr f j`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Increments.lean#L86-L108
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Increments.lean#L86-L108

import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Level_Median
import Definitions.Def_AaronsonAmbainis_Level_ThirdMoment
import Definitions.Def_AaronsonAmbainis_Level_Increments
set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Level
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Level.variance_cube_le (hTM : ThirdMomentInequality) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ)
    (ha : ∀ x j, 0 ≤ a x j) {K : ℝ} (hsum : ∀ x, ∑ j, a x j ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ j, meanAbsIncr f j ≤ M) :
    variance f ^ 3 ≤ 36 * K ^ 4 * M ^ 2 := by sorry
