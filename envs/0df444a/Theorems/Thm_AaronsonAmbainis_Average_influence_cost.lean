-- Prove2me | Theorems.Thm_AaronsonAmbainis_Average_influence_cost
-- name    : AaronsonAmbainis.Average.influence_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:43:31.480722+00:00
-- url     : https://prove2.me/theorems/da5b9d6b-8eca-4a66-bc4d-f04eb19ddad8
-- title:
--   Average: influence cost
-- statement:
--   The bound for the influences in terms of the cost alone: if `f` has a row of cost at most
--   `K` at every point and `Var f > 0`, then some coordinate `j` has
--   `3 Var(f)^5 ≤ 3125 K^6 (Inf_j f)²`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Average/Influence.lean#L157-L164
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Average/Influence.lean#L157-L164

import Definitions.Def_AaronsonAmbainis_Average_Iterate
import Definitions.Def_AaronsonAmbainis_Average_Influence
set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Average
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Average.influence_cost (hI : InfluenceBound) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ) {K : ℝ}
    (ha : ∀ x i, 0 ≤ a x i) (hsum : ∀ x, ∑ i, a x i ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, a x i) (hvar : 0 < variance f) :
    ∃ j, 3 * variance f ^ 5 ≤ 3125 * K ^ 6 * inflR f j ^ 2 := by sorry
