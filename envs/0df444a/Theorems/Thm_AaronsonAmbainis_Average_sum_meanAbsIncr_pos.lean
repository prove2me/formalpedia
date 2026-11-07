-- Prove2me | Theorems.Thm_AaronsonAmbainis_Average_sum_meanAbsIncr_pos
-- name    : AaronsonAmbainis.Average.sum_meanAbsIncr_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:38:32.206509+00:00
-- url     : https://prove2.me/theorems/cb0288b4-1943-4d52-bfc9-8b1a526fb2d5
-- title:
--   Average: sum mean Abs Incr pos
-- statement:
--   The sum `L(f)` of the mean absolute increments of a function with rows of cost at most `K`
--   and positive variance is positive.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Average/Influence.lean#L57-L63
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Average/Influence.lean#L57-L63

import Definitions.Def_AaronsonAmbainis_Average_Iterate
import Definitions.Def_AaronsonAmbainis_Average_Influence
set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Average
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Average.sum_meanAbsIncr_pos (hMI : MeanIncrementBound) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ)
    {K : ℝ} (ha : ∀ x i, 0 ≤ a x i) (hsum : ∀ x, ∑ i, a x i ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, a x i) (hvar : 0 < variance f) :
    0 < ∑ k, meanAbsIncr f k := by sorry
