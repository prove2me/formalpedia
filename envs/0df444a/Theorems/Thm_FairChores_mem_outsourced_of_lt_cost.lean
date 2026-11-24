-- Prove2me | Theorems.Thm_FairChores_mem_outsourced_of_lt_cost
-- name    : FairChores.mem_outsourced_of_lt_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:47:34.422747+00:00
-- url     : https://prove2.me/theorems/bca049f8-57ba-4ef9-871c-20be9a64578c
-- title:
--   Fair Chores: mem outsourced of lt cost
-- statement:
--   If every part of a feasible outcome costs at most `r`, then every chore whose in-house
--   cost exceeds `r` is outsourced.  For `r = MMSᵢ` this is the manuscript's observation that
--   a chore that is too expensive for agent `i` must be outsourced in its MMS partition.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L196-L210
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L196-L210

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ}

theorem FairChores.mem_outsourced_of_lt_cost {o : Outcome T n} (hvalid : o.Valid p) (hc : ∀ t, 0 ≤ c t)
    {r : ℝ} (hle : ∀ j, cost c o j ≤ r) {t : T} (ht : r < c t) : t ∈ o.outsourced := by sorry
