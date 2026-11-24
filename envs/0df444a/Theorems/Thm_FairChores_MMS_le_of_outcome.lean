-- Prove2me | Theorems.Thm_FairChores_MMS_le_of_outcome
-- name    : FairChores.MMS_le_of_outcome
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:35:56.912686+00:00
-- url     : https://prove2.me/theorems/7dfa764d-9082-48f0-8ab0-e9fe7d11ba99
-- title:
--   Fair Chores: MMS le of outcome
-- statement:
--   If some feasible outcome costs every part at most `r`, then `MMS ≤ r`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresMMSPartition.lean#L50-L52
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresMMSPartition.lean#L50-L52

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresMMSPartition
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}

theorem FairChores.MMS_le_of_outcome {c p : T → ℝ} (hc : ∀ t, 0 ≤ c t) (hn : 0 < n) {o : Outcome T n}
    (hvalid : o.Valid p) {r : ℝ} (hle : ∀ j, cost c o j ≤ r) : MMS n c p ≤ r := by sorry
