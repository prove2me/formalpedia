-- Prove2me | Theorems.Thm_FairChores_cost_le_of_outsourced_empty
-- name    : FairChores.cost_le_of_outsourced_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:20:43.984947+00:00
-- url     : https://prove2.me/theorems/d79bca22-8890-4493-9130-e36f4def7a81
-- title:
--   Fair Chores: cost le of outsourced empty
-- statement:
--   Without outsourcing, no chore costs more than the value guaranteed by the partition: the
--   property that underlies the classical bag-filling `2`-approximation for indivisible chores
--   (Algorithm 12 of the manuscript).
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L215-L220
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L215-L220

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ}

theorem FairChores.cost_le_of_outsourced_empty {o : Outcome T n} (hvalid : o.Valid p) (hc : ∀ t, 0 ≤ c t)
    (hempty : o.outsourced = ∅) {r : ℝ} (hle : ∀ j, cost c o j ≤ r) (t : T) : c t ≤ r := by sorry
