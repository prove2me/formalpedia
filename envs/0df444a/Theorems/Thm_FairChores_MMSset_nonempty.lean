-- Prove2me | Theorems.Thm_FairChores_MMSset_nonempty
-- name    : FairChores.MMSset_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:47:32.485331+00:00
-- url     : https://prove2.me/theorems/26301c2e-4ce2-4e90-9a97-cfc0743ec8c6
-- title:
--   Fair Chores: MMSset nonempty
-- statement:
--   Outsourcing nothing and giving every chore to agent `0` is feasible, so `MMSset` is
--   nonempty.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L171-L185
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L171-L185

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ}

theorem FairChores.MMSset_nonempty (hc : ∀ t, 0 ≤ c t) (hn : 0 < n) : (MMSset n c p).Nonempty := by sorry
