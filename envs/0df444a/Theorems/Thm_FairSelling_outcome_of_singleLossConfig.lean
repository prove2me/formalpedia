-- Prove2me | Theorems.Thm_FairSelling_outcome_of_singleLossConfig
-- name    : FairSelling.outcome_of_singleLossConfig
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:07:17.631804+00:00
-- url     : https://prove2.me/theorems/26780713-98bb-474f-8234-f9961086a711
-- title:
--   Fair Selling: outcome of single Loss Config
-- statement:
--   A single loss event, together with Lemma 4, yields a complete `3/4`-MMS allocation.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L672-L689
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L672-L689

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

theorem FairSelling.outcome_of_singleLossConfig (hL4 : LemmaFourCash G) (v : Fin 3 → G → ℝ) (p : G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (hnobig : ∀ i g, vbar (v i) p g < (3 / 4 : ℝ) * MMS 3 (v i) p)
    (h : SingleLossConfig v p) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by sorry
