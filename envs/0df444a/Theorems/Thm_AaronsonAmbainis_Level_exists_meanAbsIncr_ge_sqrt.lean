-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_exists_meanAbsIncr_ge_sqrt
-- name    : AaronsonAmbainis.Level.exists_meanAbsIncr_ge_sqrt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:10:00.430732+00:00
-- url     : https://prove2.me/theorems/8b2b2020-77e1-470a-ab8a-dc189cb3da9b
-- title:
--   Level: exists mean Abs Incr ge sqrt
-- statement:
--   The bound for the mean absolute increments with the power `3/2` written as `Var · √Var`:
--   some coordinate `j` has `Var(f)^{3/2} ≤ 6 K² L_j`, that is, `L_j ≥ Var(f)^{3/2} / (6 K²)`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Increments.lean#L153-L158
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Increments.lean#L153-L158

import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Level_Median
import Definitions.Def_AaronsonAmbainis_Level_ThirdMoment
import Definitions.Def_AaronsonAmbainis_Level_Increments
set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Level
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Level.exists_meanAbsIncr_ge_sqrt (hMI : MeanIncrementBound) (f : Cube ι → ℝ)
    (a : Cube ι → ι → ℝ) (ha : ∀ x j, 0 ≤ a x j) {K : ℝ} (hsum : ∀ x, ∑ j, a x j ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) (hvar : 0 < variance f) :
    ∃ j, variance f * Real.sqrt (variance f) ≤ 6 * K ^ 2 * meanAbsIncr f j := by sorry
