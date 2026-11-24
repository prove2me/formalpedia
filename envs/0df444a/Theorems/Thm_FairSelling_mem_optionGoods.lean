-- Prove2me | Theorems.Thm_FairSelling_mem_optionGoods
-- name    : FairSelling.mem_optionGoods
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:15:17.335775+00:00
-- url     : https://prove2.me/theorems/89abbb1e-18b0-4b47-b6c4-b24164de397f
-- title:
--   Fair Selling: mem option Goods
-- statement:
--   The Fair Selling construction uses the mem option Goods property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCashComposition.lean#L25-L28
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCashComposition.lean#L25-L28

import Mathlib
import Definitions.Def_RequestProject_ThreeAgentCash
import Definitions.Def_RequestProject_ThreeAgentCashComposition
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.mem_optionGoods {s : Finset (Option G)} {g : G} :
    g ∈ optionGoods s ↔ some g ∈ s := by sorry
