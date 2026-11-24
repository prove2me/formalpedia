-- Prove2me | Theorems.Thm_FairChores_equal_share_le_of_le_nsmul
-- name    : FairChores.equal_share_le_of_le_nsmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:18:42.209205+00:00
-- url     : https://prove2.me/theorems/fbd3b5ae-e4ff-413f-bcd7-251f0eaa247b
-- title:
--   Fair Chores: equal share le of le nsmul
-- statement:
--   If the outsourcing bill `W` is at most `k · MMSᵢ`, sharing it equally among the `k` active
--   agents costs each of them at most `MMSᵢ`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresBagFilling.lean#L52-L56
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresBagFilling.lean#L52-L56

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

theorem FairChores.equal_share_le_of_le_nsmul {W m : ℝ} {k : ℕ} (hk : 1 ≤ k) (hW : W ≤ k * m) :
    W / k ≤ m := by sorry
