-- Prove2me | Theorems.Thm_FairChores_SEF1_of_EF
-- name    : FairChores.SEF1_of_EF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:21:40.703943+00:00
-- url     : https://prove2.me/theorems/89c7506b-3332-4498-8666-7999ae6e8e1a
-- title:
--   Fair Chores: SEF1 of EF
-- statement:
--   `SEF1` is a genuine relaxation of envy-freeness.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresEnvy.lean#L104-L105
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresEnvy.lean#L104-L105

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable {c : Fin n → T → ℝ} {p : T → ℝ} {o : Outcome T n}
omit [Fintype T] [DecidableEq T]

theorem FairChores.SEF1_of_EF (h : EF c p o) : SEF1 c p o := by sorry
