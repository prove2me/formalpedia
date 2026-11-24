-- Prove2me | Theorems.Thm_FairSelling_MMS2_cash_of_total
-- name    : FairSelling.MMS2_cash_of_total
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:43:49.958242+00:00
-- url     : https://prove2.me/theorems/e07a41b4-8690-4f87-9af3-b06d0340e84b
-- title:
--   Fair Selling: MMS2 cash of total
-- statement:
--   The Fair Selling construction uses the MMS2 cash of total property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCash.lean#L182-L203
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCash.lean#L182-L203

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_ThreeAgentCash
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.MMS2_cash_of_total (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (R : Finset G) (cash τ : ℝ) (hcash : 0 ≤ cash) (hτ : 0 ≤ τ)
    (hsmall : ∀ g ∈ R, vbar w p g ≤ τ)
    (htotal : 3 * τ ≤ vbarSum w p R + cash) :
    τ ≤ MMS 2 (cashVal R w) (cashPrice R p cash) := by sorry
