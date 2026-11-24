-- Prove2me | Theorems.Thm_FairSelling_dropCashOutcome_kept_disjoint
-- name    : FairSelling.dropCashOutcome_kept_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:05:48.18626+00:00
-- url     : https://prove2.me/theorems/c3fc035e-b383-4193-a06f-8f5487de4eeb
-- title:
--   Fair Selling: drop Cash Outcome kept disjoint
-- statement:
--   The Fair Selling construction uses the drop Cash Outcome kept disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCashComposition.lean#L67-L70
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCashComposition.lean#L67-L70

import Mathlib
import Definitions.Def_RequestProject_ThreeAgentCash
import Definitions.Def_RequestProject_ThreeAgentCashComposition
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.dropCashOutcome_kept_disjoint (o : Outcome (Option G) 2)
    (h : ∀ i j, i ≠ j → Disjoint (o.kept i) (o.kept j)) :
    ∀ i j, i ≠ j → Disjoint ((dropCashOutcome o).kept i) ((dropCashOutcome o).kept j) := by sorry
