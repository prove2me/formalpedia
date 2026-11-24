-- Prove2me | Theorems.Thm_FairSelling_reject_one_counting
-- name    : FairSelling.reject_one_counting
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:06:47.815737+00:00
-- url     : https://prove2.me/theorems/7a5004dd-5e6f-417c-b55c-881f504acc96
-- title:
--   Fair Selling: reject one counting
-- statement:
--   **Counting after rejecting one bundle.**  If an agent values a bundle `K` plus money `m` at
--   most `3/4 · MMS`, and values the force-sold set at most `2 · (3/4 · MMS)`, then what is left after
--   removing the bundle and the sold goods is worth at least `3/4 · MMS + m` to it.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L414-L434
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L414-L434

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

theorem FairSelling.reject_one_counting (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (K S : Finset G) (m : ℝ)
    (hS : vbarSum w p S ≤ 2 * ((3 / 4 : ℝ) * MMS 3 w p))
    (hrej : vbarSum w p K + m ≤ (3 / 4 : ℝ) * MMS 3 w p) :
    (3 / 4 : ℝ) * MMS 3 w p + m ≤ vbarSum w p (Finset.univ \ (K ∪ S)) := by sorry
