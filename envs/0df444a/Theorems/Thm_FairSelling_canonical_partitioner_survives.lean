-- Prove2me | Theorems.Thm_FairSelling_canonical_partitioner_survives
-- name    : FairSelling.canonical_partitioner_survives
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:06:45.59826+00:00
-- url     : https://prove2.me/theorems/d621088f-d9f7-493f-9b37-ab13f4b24191
-- title:
--   Fair Selling: canonical partitioner survives
-- statement:
--   **The partitioning agent survives a bundle loss.**  Suppose the partitioning agent's canonical
--   partition has bundle `k` handed out, funded by selling a subset `Sa ⊆ sold` whose proceeds cover
--   the bundle's money share, with the unused proceeds banked as cash.  Then the partitioning agent
--   can still split the remaining goods and cash into two parts worth `τ` each: its two other bundles
--   survive, the goods of `sold \ Sa` being sellable inside the remainder.
--
--   Note that this holds whether the bundle is worth exactly `τ` or more to the partitioning agent.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L328-L367
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L328-L367

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

theorem FairSelling.canonical_partitioner_survives (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    {τ : ℝ} {kept : Fin 3 → Finset G} {sold : Finset G} {money : Fin 3 → ℝ} {lo : Fin 3}
    (hcan : IsCanonical w p τ kept sold money lo)
    (k : Fin 3) (Sa : Finset G) (hSa : Sa ⊆ sold) (hfund : money k ≤ ∑ g ∈ Sa, p g) :
    τ ≤ MMS 2 (cashVal (Finset.univ \ (kept k ∪ Sa)) w)
      (cashPrice (Finset.univ \ (kept k ∪ Sa)) p ((∑ g ∈ Sa, p g) - money k)) := by sorry
