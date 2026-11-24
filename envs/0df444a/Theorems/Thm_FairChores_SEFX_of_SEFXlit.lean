-- Prove2me | Theorems.Thm_FairChores_SEFX_of_SEFXlit
-- name    : FairChores.SEFX_of_SEFXlit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:21:48.537402+00:00
-- url     : https://prove2.me/theorems/a09f92cc-8960-4e66-b252-b114f876f0d8
-- title:
--   Fair Chores: SEFX of SEFXlit
-- statement:
--   The literal reading of Definition 9.2 implies the corrected `SEFX`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresEnvy.lean#L124-L130
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresEnvy.lean#L124-L130

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable {c : Fin n → T → ℝ} {p : T → ℝ} {o : Outcome T n}
omit [Fintype T] [DecidableEq T]

theorem FairChores.SEFX_of_SEFXlit (h : SEFXlit c p o) : SEFX c p o := by sorry
