-- Prove2me | Theorems.Thm_FairSelling_MMS_mem
-- name    : FairSelling.MMS_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:51:41.147897+00:00
-- url     : https://prove2.me/theorems/2a6e3d75-7d56-4041-9f61-b6e6f98afd61
-- title:
--   Fair Selling: MMS mem
-- statement:
--   **Attainment of the maximin share.** The supremum defining `MMS` is attained: there is a
--   valid outcome giving every agent (part) at least the value `MMS n v p`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/SmallN.lean#L217-L228
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/SmallN.lean#L217-L228

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}

theorem FairSelling.MMS_mem (hn : 0 < n) (v p : G → ℝ) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    MMS n v p ∈ MMSset n v p := by sorry
