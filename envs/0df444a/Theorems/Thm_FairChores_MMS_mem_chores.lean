-- Prove2me | Theorems.Thm_FairChores_MMS_mem_chores
-- name    : FairChores.MMS_mem_chores
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:20:40.921429+00:00
-- url     : https://prove2.me/theorems/eb67804a-a9a7-456d-bfb3-edf61c7fee37
-- title:
--   Fair Chores: MMS mem chores
-- statement:
--   **Attainment of the maximin share for chores.**
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresMMSPartition.lean#L258-L268
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresMMSPartition.lean#L258-L268

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresMMSPartition
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}

theorem FairChores.MMS_mem_chores (hn : 0 < n) (c p : T → ℝ) (hc : ∀ t, 0 ≤ c t) (hp : ∀ t, 0 ≤ p t) :
    MMS n c p ∈ MMSset n c p := by sorry
