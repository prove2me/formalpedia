-- Prove2me | Theorems.Thm_AaronsonAmbainis_influence_of_meanIncrement
-- name    : AaronsonAmbainis.influence_of_meanIncrement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:42:52.847183+00:00
-- url     : https://prove2.me/theorems/8cfe09a6-7aff-4eda-bc23-b5e556e72401
-- title:
--   Aaronson Ambainis: influence of mean Increment
-- statement:
--   The bound for the influences (Theorem 8.3 of the paper) from the bound for the mean absolute
--   increments (Theorem 7.10): if `f` has a row of cost at most `K` at every point and `Var f > 0`,
--   then some coordinate `j` has `3 Var(f)^5 ≤ 3125 L(f)² K^4 (Inf_j f)²`, where
--   `L(f) = ∑_k L_k(f)`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Average/Influence.lean#L71-L131
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Average/Influence.lean#L71-L131

import Definitions.Def_AaronsonAmbainis_Average_Iterate
import Definitions.Def_AaronsonAmbainis_Average_Influence
set_option autoImplicit true
open AaronsonAmbainis
open Finset

theorem AaronsonAmbainis.influence_of_meanIncrement : MeanIncrementBound → InfluenceBound := by sorry
