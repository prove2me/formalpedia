-- Prove2me | Theorems.Thm_FairSelling_dropCashOutcome_budget
-- name    : FairSelling.dropCashOutcome_budget
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:05:55.731733+00:00
-- url     : https://prove2.me/theorems/fe2c57da-ab95-496f-93a1-95e6afaef562
-- title:
--   Fair Selling: drop Cash Outcome budget
-- statement:
--   The Fair Selling construction uses the drop Cash Outcome budget property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCashComposition.lean#L75-L82
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCashComposition.lean#L75-L82

import Mathlib
import Definitions.Def_RequestProject_ThreeAgentCash
import Definitions.Def_RequestProject_ThreeAgentCashComposition
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.dropCashOutcome_budget (R : Finset G) (p : G → ℝ) (cash : ℝ)
    (o : Outcome (Option G) 2) (hcash : 0 ≤ cash)
    (hbudget : ∑ i, o.money i ≤ ∑ x ∈ o.sold, cashPrice R p cash x) :
    ∑ i, (dropCashOutcome o).money i ≤
      (∑ g ∈ (dropCashOutcome o).sold, restrictVal R p g) + cash := by sorry
