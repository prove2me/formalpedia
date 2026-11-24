-- Prove2me | Theorems.Thm_FairSelling_dropCashOutcome_sold_disjoint
-- name    : FairSelling.dropCashOutcome_sold_disjoint
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:05:46.766815+00:00
-- url     : https://prove2.me/theorems/69c1db97-6559-4d57-add8-2840ff8aea19
-- title:
--   Fair Selling: drop Cash Outcome sold disjoint
-- statement:
--   The Fair Selling construction uses the drop Cash Outcome sold disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCashComposition.lean#L62-L65
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCashComposition.lean#L62-L65

import Mathlib
import Definitions.Def_RequestProject_ThreeAgentCash
import Definitions.Def_RequestProject_ThreeAgentCashComposition
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.dropCashOutcome_sold_disjoint (o : Outcome (Option G) 2)
    (h : ∀ i, Disjoint o.sold (o.kept i)) :
    ∀ i, Disjoint (dropCashOutcome o).sold ((dropCashOutcome o).kept i) := by sorry
