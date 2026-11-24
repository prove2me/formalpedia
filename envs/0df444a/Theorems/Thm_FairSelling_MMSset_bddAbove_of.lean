-- Prove2me | Theorems.Thm_FairSelling_MMSset_bddAbove_of
-- name    : FairSelling.MMSset_bddAbove_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:27:22.065911+00:00
-- url     : https://prove2.me/theorems/3d1697cf-884c-4fe9-80cb-71ea3e4d8c3d
-- title:
--   Fair Selling: MMSset bdd Above of
-- statement:
--   The set of guaranteeable values is bounded above (needed to compare with the supremum).
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L241-L246
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L241-L246

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.MMSset_bddAbove_of (hn : 0 < n) (v p : G → ℝ) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    BddAbove (MMSset n v p) := by sorry
