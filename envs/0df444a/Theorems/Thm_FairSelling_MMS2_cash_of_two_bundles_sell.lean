-- Prove2me | Theorems.Thm_FairSelling_MMS2_cash_of_two_bundles_sell
-- name    : FairSelling.MMS2_cash_of_two_bundles_sell
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:44:48.140905+00:00
-- url     : https://prove2.me/theorems/0385935d-b6b1-449e-9f35-02b02ac0a1cc
-- title:
--   Fair Selling: MMS2 cash of two bundles sell
-- statement:
--   **Two bundles with banked cash and a sellable reserve.**  If the remainder `R` contains two
--   disjoint bundles `C, D` and a further disjoint set `T` whose goods may be sold, and the banked
--   cash `c` together with the proceeds of `T` can top both bundles up to `τ`, then the two-agent
--   maximin share of the cash-augmented remainder is at least `τ`.
--
--   This strengthens `MMS2_cash_of_two_bundles` (the case `T = ∅`): the proceeds of `T` are divisible,
--   so they may be split between the two bundles.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L94-L146
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L94-L146

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_Matching
import Definitions.Def_RequestProject_ThreeAgentCashComposition
import Definitions.Def_RequestProject_MatchingPhase
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.MMS2_cash_of_two_bundles_sell (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (R C D T : Finset G) (c c0 c1 τ : ℝ)
    (hCD : Disjoint C D) (hCT : Disjoint C T) (hDT : Disjoint D T)
    (hCR : C ⊆ R) (hDR : D ⊆ R) (hTR : T ⊆ R)
    (hc : 0 ≤ c) (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1)
    (hbudget : c0 + c1 ≤ c + ∑ g ∈ T, p g)
    (hC : τ ≤ vbarSum w p C + c0) (hD : τ ≤ vbarSum w p D + c1) :
    τ ≤ MMS 2 (cashVal R w) (cashPrice R p c) := by sorry
