-- Prove2me | Theorems.Thm_FairSelling_fin3_sum
-- name    : FairSelling.fin3_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:18:23.421958+00:00
-- url     : https://prove2.me/theorems/8b9b6c41-71dd-4b78-8f8e-e714c314f09f
-- title:
--   Fair Selling: fin3 sum
-- statement:
--   Summing over `Fin 3` in terms of three distinct indices.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L78-L86
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L78-L86

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.fin3_sum {M : Type*} [AddCommMonoid M] {a b c : Fin 3}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Fin 3 → M) :
    ∑ i, f i = f a + f b + f c := by sorry
