-- Prove2me | Theorems.Thm_FairSelling_sum_cashVal_optionGoods
-- name    : FairSelling.sum_cashVal_optionGoods
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:05:43.748803+00:00
-- url     : https://prove2.me/theorems/4dec38a1-3306-4ea2-94cc-aba9dd6db1fc
-- title:
--   Fair Selling: sum cash Val option Goods
-- statement:
--   The Fair Selling construction uses the sum cash Val option Goods property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCashComposition.lean#L46-L54
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCashComposition.lean#L46-L54

import Mathlib
import Definitions.Def_RequestProject_ThreeAgentCash
import Definitions.Def_RequestProject_ThreeAgentCashComposition
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.sum_cashVal_optionGoods (R : Finset G) (w : G → ℝ) (s : Finset (Option G)) :
    ∑ g ∈ optionGoods s, restrictVal R w g = ∑ x ∈ s, cashVal R w x := by sorry
