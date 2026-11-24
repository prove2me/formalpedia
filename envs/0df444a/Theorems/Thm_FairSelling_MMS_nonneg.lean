-- Prove2me | Theorems.Thm_FairSelling_MMS_nonneg
-- name    : FairSelling.MMS_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:14:16.267691+00:00
-- url     : https://prove2.me/theorems/19b14bbe-09b9-451f-9d07-0c965e8ae4c0
-- title:
--   Fair Selling: MMS nonneg
-- statement:
--   `MMS` is non-negative (the empty outcome guarantees `0`).
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L359-L361
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L359-L361

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.MMS_nonneg (hn : 0 < n) (v p : G → ℝ) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    0 ≤ MMS n v p := by sorry
