-- Prove2me | Theorems.Thm_FairSelling_le_MMS_of_outcome
-- name    : FairSelling.le_MMS_of_outcome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:14:00.127018+00:00
-- url     : https://prove2.me/theorems/55e5fc0d-ca70-451c-bbfd-0faf4b7a2ae3
-- title:
--   Fair Selling: le MMS of outcome
-- statement:
--   If a valid outcome guarantees value `r` to every part, then `r ≤ MMS`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L249-L252
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L249-L252

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.le_MMS_of_outcome (hn : 0 < n) (v p : G → ℝ) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g)
    (o : Outcome G n) (ho : o.Valid p) (r : ℝ) (hr : ∀ j, r ≤ util v o j) :
    r ≤ MMS n v p := by sorry
