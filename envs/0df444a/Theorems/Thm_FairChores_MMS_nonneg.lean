-- Prove2me | Theorems.Thm_FairChores_MMS_nonneg
-- name    : FairChores.MMS_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:16:43.131865+00:00
-- url     : https://prove2.me/theorems/122cf9d8-4387-4c58-b248-413bdf04f627
-- title:
--   Fair Chores: MMS nonneg
-- statement:
--   The maximin share is non-negative.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L188-L191
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L188-L191

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ}

theorem FairChores.MMS_nonneg (hc : ∀ t, 0 ≤ c t) (hn : 0 < n) : 0 ≤ MMS n c p := by sorry
