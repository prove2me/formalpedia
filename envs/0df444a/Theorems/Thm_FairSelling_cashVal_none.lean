-- Prove2me | Theorems.Thm_FairSelling_cashVal_none
-- name    : FairSelling.cashVal_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:14:16.764077+00:00
-- url     : https://prove2.me/theorems/664fdcb3-9daa-42c9-bcb6-62fafd26ca2c
-- title:
--   Fair Selling: cash Val none
-- statement:
--   The Fair Selling construction uses the cash Val none property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCash.lean#L33-L33
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCash.lean#L33-L33

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_ThreeAgentCash
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.cashVal_none (R : Finset G) (w : G → ℝ) : cashVal R w none = 0 := by sorry

attribute [defeq] FairSelling.cashVal_none
