-- Prove2me | Theorems.Thm_FairSelling_matching_fin3
-- name    : FairSelling.matching_fin3
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:56:05.963544+00:00
-- url     : https://prove2.me/theorems/cf7f03c5-0ead-469b-a076-7928aa32420b
-- title:
--   Fair Selling: matching fin3
-- statement:
--   **Hall's theorem for three agents (matching step, `n = 3`).**
--   Let `acc j k` record whether agent `j` accepts bundle `k`.  Assume the partitioning agent `pa`
--   accepts every bundle, and that no agent rejects all three bundles.  Then either
--
--   * there is a **perfect matching**: a permutation `σ` of `Fin 3` with agent `j` accepting bundle
--     `σ j` for every `j`; or
--   * there is a **single loss event**: a bundle `k` accepted by the partitioning agent `pa` but
--     rejected by both other agents.
--
--   This is the `n = 3` special case of Hall's marriage theorem that drives the matching step of the
--   manuscript's `3/4`-MMS algorithm, proved by exhaustive case analysis.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Matching.lean#L41-L47
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Matching.lean#L41-L47

import Mathlib
import Definitions.Def_RequestProject_Matching
set_option autoImplicit true
open FairSelling
set_option maxRecDepth 4000

theorem FairSelling.matching_fin3 (acc : Fin 3 → Fin 3 → Bool) (pa : Fin 3)
    (hpa : ∀ k, acc pa k = true)
    (hnorej : ∀ j, ∃ k, acc j k = true) :
    (∃ σ : Equiv.Perm (Fin 3), ∀ j, acc j (σ j) = true)
    ∨ (∃ k, acc pa k = true ∧ ∀ j, j ≠ pa → acc j k = false) := by sorry
