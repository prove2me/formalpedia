-- Prove2me | Theorems.Thm_FairSelling_outcome_of_bundles
-- name    : FairSelling.outcome_of_bundles
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:33:44.905387+00:00
-- url     : https://prove2.me/theorems/986d596d-6388-47a0-919a-24b11d181740
-- title:
--   Fair Selling: outcome of bundles
-- statement:
--   Turning three pairwise disjoint bundles (with money financed by a force-sold set) into a valid
--   three-agent outcome.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L244-L253
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L244-L253

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

theorem FairSelling.outcome_of_bundles (v : Fin 3 → G → ℝ) (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    (X : Fin 3 → Finset G) (F : Finset G) (q : Fin 3 → ℝ)
    (hX : ∀ i j, i ≠ j → Disjoint (X i) (X j)) (hF : ∀ i, Disjoint F (X i))
    (hq0 : ∀ i, 0 ≤ q i) (hq : ∑ i, q i ≤ ∑ g ∈ F, p g)
    (hval : ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ vbarSum (v i) p (X i) + q i) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by sorry
