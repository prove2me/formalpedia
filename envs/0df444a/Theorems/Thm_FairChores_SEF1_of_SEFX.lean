-- Prove2me | Theorems.Thm_FairChores_SEF1_of_SEFX
-- name    : FairChores.SEF1_of_SEFX
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:21:40.681465+00:00
-- url     : https://prove2.me/theorems/f265833e-6ff3-4893-b262-b00b0e47aebe
-- title:
--   Fair Chores: SEF1 of SEFX
-- statement:
--   `SEFX` implies `SEF1`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresEnvy.lean#L108-L120
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresEnvy.lean#L108-L120

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable {c : Fin n → T → ℝ} {p : T → ℝ} {o : Outcome T n}

theorem FairChores.SEF1_of_SEFX (hc : ∀ i t, 0 ≤ c i t) (hp : ∀ t, 0 ≤ p t)
    (hvalid : o.Valid p) (h : SEFX c p o) : SEF1 c p o := by sorry
