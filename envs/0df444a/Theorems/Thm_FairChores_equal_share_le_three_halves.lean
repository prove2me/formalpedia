-- Prove2me | Theorems.Thm_FairChores_equal_share_le_three_halves
-- name    : FairChores.equal_share_le_three_halves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:19:17.942156+00:00
-- url     : https://prove2.me/theorems/00dcd18d-0508-43ef-9fd4-a5da1708c9e3
-- title:
--   Fair Chores: equal share le three halves
-- statement:
--   The manuscript's bound for the outsourcing step (line 17 of Algorithm 13): if the bill is
--   at most `(k+1) · MMSᵢ` and at least two agents are still active, sharing it equally costs each
--   of them at most `3/2 · MMSᵢ` — this is the inequality `(n−k+1)/(n−k) ≤ 3/2`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresBagFilling.lean#L61-L66
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresBagFilling.lean#L61-L66

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresPreAlloc
import Definitions.Def_RequestProject_ChoresBagLemma
import Definitions.Def_RequestProject_ChoresBagFilling
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable {c : Fin n → T → ℝ} {p : T → ℝ} {mu : Fin n → ℝ}

theorem FairChores.equal_share_le_three_halves {W m : ℝ} {k : ℕ} (hk : 2 ≤ k) (hm : 0 ≤ m)
    (hW : W ≤ (k + 1) * m) : W / k ≤ 3 / 2 * m := by sorry
