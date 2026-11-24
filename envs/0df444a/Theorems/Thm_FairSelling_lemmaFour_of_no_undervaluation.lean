-- Prove2me | Theorems.Thm_FairSelling_lemmaFour_of_no_undervaluation
-- name    : FairSelling.lemmaFour_of_no_undervaluation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:06:46.703042+00:00
-- url     : https://prove2.me/theorems/0cf08d11-4423-4511-ba79-9cd29b736d8f
-- title:
--   Fair Selling: lemma Four of no undervaluation
-- statement:
--   **The easy branch of Lemma 4.**  If the agent does not value the force-sold goods above
--   their market price, then no value at all is destroyed by the sale, and the cash-augmented
--   remainder still has total value at least `3 · (3/4 · MMS)`; bag filling then splits it into two
--   acceptable parts.  This covers in particular the case of a *pure* bundle (nothing is sold).
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L619-L636
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L619-L636

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

theorem FairSelling.lemmaFour_of_no_undervaluation (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (hnobig : ∀ g, vbar w p g < (3 / 4 : ℝ) * MMS 3 w p)
    (K S : Finset G) (m : ℝ) (hKS : Disjoint K S) (hmS : m ≤ ∑ g ∈ S, p g)
    (hS : vbarSum w p S ≤ ∑ g ∈ S, p g)
    (hrej : vbarSum w p K + m ≤ (3 / 4 : ℝ) * MMS 3 w p) :
    (3 / 4 : ℝ) * MMS 3 w p ≤ MMS 2 (cashVal (Finset.univ \ (K ∪ S)) w)
      (cashPrice (Finset.univ \ (K ∪ S)) p ((∑ g ∈ S, p g) - m)) := by sorry
