-- Prove2me | Theorems.Thm_AaronsonAmbainis_Average_influence_of_incr
-- name    : AaronsonAmbainis.Average.influence_of_incr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:38:47.376722+00:00
-- url     : https://prove2.me/theorems/a490dc7c-c8ac-4ed5-8c1f-d8290a4129ac
-- title:
--   Average: influence of incr
-- statement:
--   The bound for the influences with a bound `G` for the sums of the increments at the points:
--   `3 Var(f)^5 ≤ 3125 G² K^4 (Inf_j f)²`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Average/Influence.lean#L139-L152
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Average/Influence.lean#L139-L152

import Definitions.Def_AaronsonAmbainis_Average_Iterate
import Definitions.Def_AaronsonAmbainis_Average_Influence
set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Average
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Average.influence_of_incr (hI : InfluenceBound) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ) {K G : ℝ}
    (ha : ∀ x i, 0 ≤ a x i) (hsum : ∀ x, ∑ i, a x i ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, a x i)
    (hG : ∀ u, ∑ j, |f u - f (flipSet u {j})| ≤ G) (hvar : 0 < variance f) :
    ∃ j, 3 * variance f ^ 5 ≤ 3125 * G ^ 2 * K ^ 4 * inflR f j ^ 2 := by sorry
