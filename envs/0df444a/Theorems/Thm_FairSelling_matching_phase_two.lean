-- Prove2me | Theorems.Thm_FairSelling_matching_phase_two
-- name    : FairSelling.matching_phase_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:06:08.590793+00:00
-- url     : https://prove2.me/theorems/5db5c928-203c-4d7e-bca4-1e2fca501e5f
-- title:
--   Fair Selling: matching phase two
-- statement:
--   **The matching phase, combinatorially.**  Two agents (`Fin 2`) are matched against the two
--   non-leftovers bundles (`Fin 2`), agent `j` accepting bundle `k` iff `acc j k = true`.  Then
--   exactly one of the following happens:
--
--   * a **perfect matching** exists;
--   * some bundle is **rejected by both** agents;
--   * one agent accepts **both** bundles and the other agent accepts **neither** — the special case.
--
--   Proved by exhaustive case analysis.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L66-L71
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L66-L71

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

theorem FairSelling.matching_phase_two (acc : Fin 2 → Fin 2 → Bool) :
    (∃ σ : Equiv.Perm (Fin 2), ∀ j, acc j (σ j) = true)
    ∨ (∃ k, ∀ j, acc j k = false)
    ∨ (∃ j j' : Fin 2, j ≠ j' ∧ (∀ k, acc j k = true) ∧ (∀ k, acc j' k = false)) := by sorry
