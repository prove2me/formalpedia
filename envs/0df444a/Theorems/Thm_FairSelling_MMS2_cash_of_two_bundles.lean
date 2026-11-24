-- Prove2me | Theorems.Thm_FairSelling_MMS2_cash_of_two_bundles
-- name    : FairSelling.MMS2_cash_of_two_bundles
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:05:31.770878+00:00
-- url     : https://prove2.me/theorems/7a4b1704-ae9a-4d42-b82c-ea56ac6a4926
-- title:
--   Fair Selling: MMS2 cash of two bundles
-- statement:
--   The Fair Selling construction uses the MMS2 cash of two bundles property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCash.lean#L60-L89
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCash.lean#L60-L89

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_ThreeAgentCash
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.MMS2_cash_of_two_bundles (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (R C D : Finset G) (c c0 c1 τ : ℝ)
    (hCD : Disjoint C D) (hCR : C ⊆ R) (hDR : D ⊆ R)
    (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (hcash : c0 + c1 ≤ c)
    (hC : τ ≤ vbarSum w p C + c0) (hD : τ ≤ vbarSum w p D + c1) :
    τ ≤ MMS 2 (cashVal R w) (cashPrice R p c) := by sorry
