-- Prove2me | Theorems.Thm_FairChores_SEF1_of_SEF1lit
-- name    : FairChores.SEF1_of_SEF1lit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:21:50.240639+00:00
-- url     : https://prove2.me/theorems/2d3a6ec5-d806-4c15-ae90-b8d5b9df3b84
-- title:
--   Fair Chores: SEF1 of SEF1lit
-- statement:
--   The literal reading of Definition 9.1 implies the corrected `SEF1`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresEnvy.lean#L134-L139
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresEnvy.lean#L134-L139

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable {c : Fin n → T → ℝ} {p : T → ℝ} {o : Outcome T n}
omit [Fintype T] [DecidableEq T]

theorem FairChores.SEF1_of_SEF1lit (h : SEF1lit c p o) : SEF1 c p o := by sorry
