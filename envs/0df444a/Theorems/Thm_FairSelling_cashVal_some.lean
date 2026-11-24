-- Prove2me | Theorems.Thm_FairSelling_cashVal_some
-- name    : FairSelling.cashVal_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:14:45.452733+00:00
-- url     : https://prove2.me/theorems/cd7e23e2-e8c4-47d1-80ab-7782342bc4e7
-- title:
--   Fair Selling: cash Val some
-- statement:
--   The Fair Selling construction uses the cash Val some property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCash.lean#L34-L35
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCash.lean#L34-L35

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_ThreeAgentCash
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.cashVal_some (R : Finset G) (w : G → ℝ) (g : G) :
    cashVal R w (some g) = restrictVal R w g := by sorry

attribute [defeq] FairSelling.cashVal_some
