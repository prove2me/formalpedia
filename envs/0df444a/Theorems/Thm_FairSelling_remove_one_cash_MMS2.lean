-- Prove2me | Theorems.Thm_FairSelling_remove_one_cash_MMS2
-- name    : FairSelling.remove_one_cash_MMS2
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:56:51.889074+00:00
-- url     : https://prove2.me/theorems/1c11eabf-c299-43fe-b09e-bc1e87ea2358
-- title:
--   Fair Selling: remove one cash MMS2
-- statement:
--   The Fair Selling construction uses the remove one cash MMS2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCash.lean#L95-L175
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCash.lean#L95-L175

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_ThreeAgentCash
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.remove_one_cash_MMS2 (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (g : G) :
    MMS 3 w p ≤ MMS 2 (cashVal (Finset.univ \ {g}) w)
      (cashPrice (Finset.univ \ {g}) p (p g)) := by sorry
