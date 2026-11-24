-- Prove2me | Theorems.Thm_FairChores_exists_MMS_partition_chores
-- name    : FairChores.exists_MMS_partition_chores
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:20:42.340535+00:00
-- url     : https://prove2.me/theorems/bad2a30c-7d14-4583-a685-ae7ec2c9be57
-- title:
--   Fair Chores: exists MMS partition chores
-- statement:
--   **An MMS partition for chores**: a feasible outcome all of whose parts cost at most the
--   maximin share.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresMMSPartition.lean#L272-L275
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresMMSPartition.lean#L272-L275

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresMMSPartition
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}

theorem FairChores.exists_MMS_partition_chores (hn : 0 < n) (c p : T → ℝ) (hc : ∀ t, 0 ≤ c t)
    (hp : ∀ t, 0 ≤ p t) :
    ∃ o : Outcome T n, o.Valid p ∧ ∀ j, cost c o j ≤ MMS n c p := by sorry
