-- Prove2me | Theorems.Thm_FairSelling_canonical_shave
-- name    : FairSelling.canonical_shave
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:59:27.843354+00:00
-- url     : https://prove2.me/theorems/fce93f06-9f66-45e1-bf17-99c49bf2c706
-- title:
--   Fair Selling: canonical shave
-- statement:
--   **Shaving a canonical partition.**  It is without loss of generality to assume that every
--   non-leftovers bundle of a canonical partition is worth *exactly* `τ` to the partitioning agent
--   (or carries no money at all): any excess sale money can be moved to the leftovers bundle.  The
--   resulting partition is still strictly canonical, and the leftovers bundle only got richer.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L171-L237
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L171-L237

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
omit [Fintype G] [DecidableEq G]

theorem FairSelling.canonical_shave (w p : G → ℝ) {τ : ℝ} {kept : Fin 3 → Finset G} {sold : Finset G}
    {money : Fin 3 → ℝ} {lo : Fin 3} (hcan : IsCanonicalStrict w p τ kept sold money lo) :
    ∃ money' : Fin 3 → ℝ, IsCanonicalStrict w p τ kept sold money' lo ∧
      (∀ k, k ≠ lo → money' k = 0 ∨ vbarSum w p (kept k) + money' k = τ) ∧
      (∀ k, k ≠ lo → money' k ≤ money k) ∧ money lo ≤ money' lo := by sorry
