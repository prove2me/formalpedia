-- Prove2me | Theorems.Thm_FairSelling_bagfill
-- name    : FairSelling.bagfill
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:23:43.760689+00:00
-- url     : https://prove2.me/theorems/54976408-72fb-4cfc-aed5-47d5696e0eac
-- title:
--   Fair Selling: bagfill
-- statement:
--   **Bag-filling.**  If every item of `S` has weight at most the interval length `hi - lo`, and
--   the total weight of `S` is at least `lo`, then some sub-bundle `B ⊆ S` has total weight in the
--   interval `[lo, hi]`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L337-L356
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L337-L356

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]

theorem FairSelling.bagfill (u : G → ℝ) (lo hi : ℝ) (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) :
    ∀ S : Finset G, (∀ g ∈ S, u g ≤ hi - lo) → lo ≤ ∑ g ∈ S, u g →
      ∃ B ⊆ S, lo ≤ ∑ g ∈ B, u g ∧ ∑ g ∈ B, u g ≤ hi := by sorry
