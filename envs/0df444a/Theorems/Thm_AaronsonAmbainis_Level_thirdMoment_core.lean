-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_thirdMoment_core
-- name    : AaronsonAmbainis.Level.thirdMoment_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:37:45.054439+00:00
-- url     : https://prove2.me/theorems/a25d1183-b190-4e22-abce-5d20a2fa3032
-- title:
--   Level: third Moment core
-- statement:
--   The third-moment inequality, unnormalised:
--   `(∑_x ((f x - s)⁺)^3) · #{y : f y ≤ s} ≤ (3/2) 4^n M K²`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/ThirdMoment.lean#L55-L194
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/ThirdMoment.lean#L55-L194

import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Level_AllPairs
import Definitions.Def_AaronsonAmbainis_TwoSided_CauchySchwarz
import Definitions.Def_AaronsonAmbainis_Level_ThirdMoment
set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Level
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Level.thirdMoment_core (hInt : IntegratedAllPairsInequality) (f : Cube ι → ℝ)
    (a : Cube ι → ι → ℝ) (ha : ∀ x j, 0 ≤ a x j) {K : ℝ} (hsum : ∀ x, ∑ j, a x j ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ j, meanAbsIncr f j ≤ M) (s : ℝ) :
    (∑ x, max (f x - s) 0 ^ 3) * ((univ.filter (fun y : Cube ι => f y ≤ s)).card : ℝ)
      ≤ 3 / 2 * 4 ^ Fintype.card ι * M * K ^ 2 := by sorry
