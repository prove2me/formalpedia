-- Prove2me | Theorems.Thm_FairSelling_money_le_proceeds
-- name    : FairSelling.money_le_proceeds
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:53:37.211901+00:00
-- url     : https://prove2.me/theorems/e4bd6a40-4cfc-4230-b6f2-9e0cd0d588ad
-- title:
--   Fair Selling: money le proceeds
-- statement:
--   In a valid outcome, each agent's money is at most the total sale proceeds.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaEleven.lean#L57-L61
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaEleven.lean#L57-L61

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
set_option autoImplicit true
open scoped BigOperators
open Filter Topology
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G] [DecidableEq G]

theorem FairSelling.money_le_proceeds {p : G → ℝ} {o : Outcome G n} (h : o.Valid p) (j : Fin n) :
    o.money j ≤ ∑ g ∈ o.sold, p g := by sorry
