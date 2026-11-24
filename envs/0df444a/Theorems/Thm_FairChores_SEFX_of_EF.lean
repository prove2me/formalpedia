-- Prove2me | Theorems.Thm_FairChores_SEFX_of_EF
-- name    : FairChores.SEFX_of_EF
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:17:09.221819+00:00
-- url     : https://prove2.me/theorems/0e8f9b86-fe75-4f8e-97a5-c77c0eb1c8a5
-- title:
--   Fair Chores: SEFX of EF
-- statement:
--   `SEFX` is a genuine relaxation of envy-freeness.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresEnvy.lean#L99-L100
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresEnvy.lean#L99-L100

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable {c : Fin n → T → ℝ} {p : T → ℝ} {o : Outcome T n}
omit [Fintype T] [DecidableEq T]

theorem FairChores.SEFX_of_EF (h : EF c p o) : SEFX c p o := by sorry
