-- Prove2me | Theorems.Thm_FairSelling_fin3_cover
-- name    : FairSelling.fin3_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:17:42.708485+00:00
-- url     : https://prove2.me/theorems/ab0ce572-d0d3-4789-a3e2-39e147f6bdd7
-- title:
--   Fair Selling: fin3 cover
-- statement:
--   Three distinct elements of `Fin 3` exhaust `Fin 3`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L73-L75
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L73-L75

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G] [DecidableEq G]

theorem FairSelling.fin3_cover {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (i : Fin 3) :
    i = a ∨ i = b ∨ i = c := by sorry
