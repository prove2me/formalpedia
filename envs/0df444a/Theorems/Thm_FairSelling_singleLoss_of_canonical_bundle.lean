-- Prove2me | Theorems.Thm_FairSelling_singleLoss_of_canonical_bundle
-- name    : FairSelling.singleLoss_of_canonical_bundle
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:06:59.164251+00:00
-- url     : https://prove2.me/theorems/d836a0a8-8564-406c-ac2c-2a8ff1a8e141
-- title:
--   Fair Selling: single Loss of canonical bundle
-- statement:
--   **Handing out one non-leftovers bundle produces a single loss event.**  Agent `x` accepts the
--   non-leftovers bundle `k` of the partitioning agent's canonical partition; the bundle is funded by
--   selling at most one good.  Every other agent is either the partitioning agent (which survives the
--   loss by `canonical_partitioner_survives`) or values the bundle at most `3/4 · MMS`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L695-L730
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L695-L730

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

theorem FairSelling.singleLoss_of_canonical_bundle (v : Fin 3 → G → ℝ) (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    (a : Fin 3) (hva : ∀ g, 0 ≤ v a g) (hmax : ∀ i, MMS 3 (v i) p ≤ MMS 3 (v a) p)
    {kept : Fin 3 → Finset G} {sold : Finset G} {money : Fin 3 → ℝ} {lo : Fin 3}
    (hcan : IsCanonicalStrict (v a) p ((3 / 4 : ℝ) * MMS 3 (v a) p) kept sold money lo)
    (k : Fin 3) (hk : k ≠ lo) (x : Fin 3)
    (hxacc : (3 / 4 : ℝ) * MMS 3 (v x) p ≤ vbarSum (v x) p (kept k) + money k)
    (hrest : ∀ i, i ≠ x → i = a ∨
      vbarSum (v i) p (kept k) + money k ≤ (3 / 4 : ℝ) * MMS 3 (v i) p) :
    SingleLossConfig v p := by sorry
