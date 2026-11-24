-- Prove2me | Theorems.Thm_FairSelling_sum_cashPrice_optionGoods
-- name    : FairSelling.sum_cashPrice_optionGoods
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:05:26.429485+00:00
-- url     : https://prove2.me/theorems/b90cc2da-bfec-44a1-8be5-fa6f1fdc2848
-- title:
--   Fair Selling: sum cash Price option Goods
-- statement:
--   The Fair Selling construction uses the sum cash Price option Goods property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCashComposition.lean#L34-L44
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCashComposition.lean#L34-L44

import Mathlib
import Definitions.Def_RequestProject_ThreeAgentCash
import Definitions.Def_RequestProject_ThreeAgentCashComposition
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.sum_cashPrice_optionGoods (R : Finset G) (p : G → ℝ) (cash : ℝ)
    (s : Finset (Option G)) :
    (∑ g ∈ optionGoods s, restrictVal R p g) + (if none ∈ s then cash else 0) =
      ∑ x ∈ s, cashPrice R p cash x := by sorry
