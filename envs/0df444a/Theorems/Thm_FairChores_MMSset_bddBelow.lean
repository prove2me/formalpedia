-- Prove2me | Theorems.Thm_FairChores_MMSset_bddBelow
-- name    : FairChores.MMSset_bddBelow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:35:21.338457+00:00
-- url     : https://prove2.me/theorems/678af547-115a-4322-9818-2de52c881757
-- title:
--   Fair Chores: MMSset bdd Below
-- statement:
--   `MMSset` is bounded below by `0` (as soon as there is at least one agent).
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L164-L167
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L164-L167

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ}

theorem FairChores.MMSset_bddBelow (hc : ∀ t, 0 ≤ c t) (hn : 0 < n) : BddBelow (MMSset n c p) := by sorry
