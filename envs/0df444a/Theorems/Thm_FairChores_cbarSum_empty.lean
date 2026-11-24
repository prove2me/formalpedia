-- Prove2me | Theorems.Thm_FairChores_cbarSum_empty
-- name    : FairChores.cbarSum_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:10:00.330329+00:00
-- url     : https://prove2.me/theorems/36838814-6f97-47b2-a031-c3167a82367b
-- title:
--   Fair Chores: cbar Sum empty
-- statement:
--   The Fair Chores construction uses the cbar Sum empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L80-L81
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L80-L81

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ}
omit [Fintype T] [DecidableEq T]

theorem FairChores.cbarSum_empty (c p : T → ℝ) : cbarSum c p (∅ : Finset T) = 0 := by sorry
