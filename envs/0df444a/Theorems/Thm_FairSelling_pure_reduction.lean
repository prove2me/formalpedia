-- Prove2me | Theorems.Thm_FairSelling_pure_reduction
-- name    : FairSelling.pure_reduction
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:39:06.411741+00:00
-- url     : https://prove2.me/theorems/f90e8e18-6c89-406b-a4cf-aeb2c69807d3
-- title:
--   Fair Selling: pure reduction
-- statement:
--   **Clean case of Lemma 4 (pure bundle).**  For an agent `i` all of whose goods have
--   `v̄`-value below `3/4 · MMS_i`, if a bundle `B` of `v̄`-value at most `3/4 · MMS_i` is removed,
--   then the remaining goods can (as a two-agent instance) still guarantee `3/4 · MMS_i`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L388-L418
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L388-L418

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.pure_reduction (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (hnobig : ∀ g, vbar w p g < (3/4) * MMS 3 w p)
    (B : Finset G) (hBrej : vbarSum w p B ≤ (3/4) * MMS 3 w p) :
    (3/4) * MMS 3 w p ≤
      MMS 2 (restrictVal (Finset.univ \ B) w) (restrictVal (Finset.univ \ B) p) := by sorry
