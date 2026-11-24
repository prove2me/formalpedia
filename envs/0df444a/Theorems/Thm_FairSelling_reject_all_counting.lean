-- Prove2me | Theorems.Thm_FairSelling_reject_all_counting
-- name    : FairSelling.reject_all_counting
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:06:49.209813+00:00
-- url     : https://prove2.me/theorems/6d772f49-e6e6-49ea-848b-09225f9899f6
-- title:
--   Fair Selling: reject all counting
-- statement:
--   **Counting after rejecting every bundle.**  If an agent values each of the three bundles of a
--   partition (goods plus money share) at most `3/4 · MMS`, then everything outside those bundles is
--   worth more than `3/4 · MMS` plus the total distributed money to it.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L386-L409
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L386-L409

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

theorem FairSelling.reject_all_counting (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (kept : Fin 3 → Finset G) (money : Fin 3 → ℝ)
    (hdisj : ∀ j k, j ≠ k → Disjoint (kept j) (kept k))
    (k0 k1 k2 : Fin 3) (h01 : k0 ≠ k1) (h02 : k0 ≠ k2) (h12 : k1 ≠ k2)
    (hrej : ∀ k, vbarSum w p (kept k) + money k ≤ (3 / 4 : ℝ) * MMS 3 w p) :
    (3 / 4 : ℝ) * MMS 3 w p + ∑ k, money k ≤
      vbarSum w p (Finset.univ \ (kept k0 ∪ kept k1 ∪ kept k2)) := by sorry
