-- Prove2me | Theorems.Thm_FairSelling_optionGoods_disjoint
-- name    : FairSelling.optionGoods_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:44:00.76814+00:00
-- url     : https://prove2.me/theorems/7b860204-2db0-4925-9ccc-e52396206424
-- title:
--   Fair Selling: option Goods disjoint
-- statement:
--   The Fair Selling construction uses the option Goods disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCashComposition.lean#L30-L32
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCashComposition.lean#L30-L32

import Mathlib
import Definitions.Def_RequestProject_ThreeAgentCash
import Definitions.Def_RequestProject_ThreeAgentCashComposition
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.optionGoods_disjoint {s t : Finset (Option G)} (h : Disjoint s t) :
    Disjoint (optionGoods s) (optionGoods t) := by sorry
