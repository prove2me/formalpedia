-- Prove2me | Theorems.Thm_FairSelling_cashPrice_none
-- name    : FairSelling.cashPrice_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:14:32.675802+00:00
-- url     : https://prove2.me/theorems/f1aad3bd-ed62-4da2-be4a-fb101bc4b390
-- title:
--   Fair Selling: cash Price none
-- statement:
--   The Fair Selling construction uses the cash Price none property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCash.lean#L36-L37
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCash.lean#L36-L37

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_ThreeAgentCash
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.cashPrice_none (R : Finset G) (p : G → ℝ) (c : ℝ) :
    cashPrice R p c none = c := by sorry

attribute [defeq] FairSelling.cashPrice_none
