-- Prove2me | Theorems.Thm_AaronsonAmbainis_Average_exists_meanAbsIncr_pos
-- name    : AaronsonAmbainis.Average.exists_meanAbsIncr_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:38:25.095701+00:00
-- url     : https://prove2.me/theorems/000cb3b7-ebc3-4c40-a368-d30bb053e26e
-- title:
--   Average: exists mean Abs Incr pos
-- statement:
--   The bound for the mean absolute increments, with the positivity of the increment that it
--   gives.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Average/Influence.lean#L42-L53
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Average/Influence.lean#L42-L53

import Definitions.Def_AaronsonAmbainis_Average_Iterate
import Definitions.Def_AaronsonAmbainis_Average_Influence
set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Average
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Average.exists_meanAbsIncr_pos (hMI : MeanIncrementBound) (g : Cube ι → ℝ) (b : Cube ι → ι → ℝ)
    {K : ℝ} (hb0 : ∀ x i, 0 ≤ b x i) (hbK : ∀ x, ∑ i, b x i ≤ K)
    (hbrow : ∀ x y, |g x - g y| ≤ ∑ i ∈ diffSet x y, b x i) (hg : 0 < variance g) :
    ∃ j, 0 < meanAbsIncr g j ∧ variance g ^ 3 ≤ 36 * K ^ 4 * meanAbsIncr g j ^ 2 := by sorry
