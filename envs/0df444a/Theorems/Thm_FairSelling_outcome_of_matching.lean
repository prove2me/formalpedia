-- Prove2me | Theorems.Thm_FairSelling_outcome_of_matching
-- name    : FairSelling.outcome_of_matching
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:59:30.764777+00:00
-- url     : https://prove2.me/theorems/bcbcfb68-d84e-4355-8f39-7726ee6e267b
-- title:
--   Fair Selling: outcome of matching
-- statement:
--   **The perfect-matching case.**  If every agent is matched to a bundle of a canonical partition
--   that it accepts, the allocation is a valid `3/4`-MMS outcome.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L258-L270
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L258-L270

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
omit [Fintype G]

theorem FairSelling.outcome_of_matching (v : Fin 3 → G → ℝ) (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    {w : G → ℝ} {τ : ℝ} {kept : Fin 3 → Finset G} {sold : Finset G} {money : Fin 3 → ℝ}
    {lo : Fin 3} (hcan : IsCanonical w p τ kept sold money lo)
    (σ : Equiv.Perm (Fin 3))
    (hacc : ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ vbarSum (v i) p (kept (σ i)) + money (σ i)) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by sorry
