-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_thirdMoment_lower
-- name    : AaronsonAmbainis.Level.thirdMoment_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:39:55.709896+00:00
-- url     : https://prove2.me/theorems/3cddbdc6-de15-44d4-8cb0-c38ba33efec4
-- title:
--   Level: third Moment lower
-- statement:
--   The third-moment inequality on the other side (Theorem 7.6 of the paper, second inequality):
--   `E[((s - f)⁺)^3] · Pr[f ≥ s] ≤ (3/2) K² M`. It is the third-moment inequality for `-f` and `-s`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/ThirdMoment.lean#L218-L254
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/ThirdMoment.lean#L218-L254

import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Level_AllPairs
import Definitions.Def_AaronsonAmbainis_TwoSided_CauchySchwarz
import Definitions.Def_AaronsonAmbainis_Level_ThirdMoment
set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Level
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Level.thirdMoment_lower (hTM : ThirdMomentInequality) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ)
    (ha : ∀ x j, 0 ≤ a x j) {K : ℝ} (hsum : ∀ x, ∑ j, a x j ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ j, meanAbsIncr f j ≤ M) (s : ℝ) :
    (∑ x, max (s - f x) 0 ^ 3) / 2 ^ Fintype.card ι
        * (((univ.filter (fun y : Cube ι => s ≤ f y)).card : ℝ) / 2 ^ Fintype.card ι)
      ≤ 3 / 2 * K ^ 2 * M := by sorry
