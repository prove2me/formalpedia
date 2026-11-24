-- Prove2me | Theorems.Thm_FairSelling_greedy_two_bags
-- name    : FairSelling.greedy_two_bags
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:32:44.372796+00:00
-- url     : https://prove2.me/theorems/534327f6-83b5-4f1e-be47-a113c6a1c551
-- title:
--   Fair Selling: greedy two bags
-- statement:
--   The Fair Selling construction uses the greedy two bags property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/CanonicalPartition.lean#L72-L107
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/CanonicalPartition.lean#L72-L107

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_Matching
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_CanonicalPartition
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]

theorem FairSelling.greedy_two_bags (u : G → ℝ) (hu : ∀ g, 0 ≤ u g)
    (τ : ℝ) (hτ : 0 < τ) (S : Finset G)
    (hsmall : ∀ g ∈ S, u g < (2/3) * τ)
    (htot : 3 * τ ≤ ∑ g ∈ S, u g) :
    ∃ B1 B2 : Finset G, B1 ⊆ S ∧ B2 ⊆ S ∧ Disjoint B1 B2 ∧
      τ ≤ ∑ g ∈ B1, u g ∧ τ ≤ ∑ g ∈ B2, u g ∧
      (∑ g ∈ B1, u g) + (∑ g ∈ B2, u g) ≤ 3 * τ := by sorry
