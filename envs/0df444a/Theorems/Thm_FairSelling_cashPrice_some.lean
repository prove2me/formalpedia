-- Prove2me | Theorems.Thm_FairSelling_cashPrice_some
-- name    : FairSelling.cashPrice_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:15:22.017156+00:00
-- url     : https://prove2.me/theorems/baab98fa-720f-4727-aae7-3a24663c0d34
-- title:
--   Fair Selling: cash Price some
-- statement:
--   The Fair Selling construction uses the cash Price some property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCash.lean#L38-L39
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCash.lean#L38-L39

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_ThreeAgentCash
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.cashPrice_some (R : Finset G) (p : G → ℝ) (c : ℝ) (g : G) :
    cashPrice R p c (some g) = restrictVal R p g := by sorry

attribute [defeq] FairSelling.cashPrice_some
