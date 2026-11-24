-- Prove2me | Theorems.Thm_FairSelling_epsSEFX_of_SEFX
-- name    : FairSelling.epsSEFX_of_SEFX
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:34:08.210589+00:00
-- url     : https://prove2.me/theorems/d461f92e-2477-41bc-9723-317651009c91
-- title:
--   Fair Selling: eps SEFX of SEFX
-- statement:
--   `SEFX` implies `ε-SEFX` for every `ε ≥ 0`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L152-L153
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L152-L153

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}

theorem FairSelling.epsSEFX_of_SEFX {eps : ℝ} (heps : 0 ≤ eps) (ho : SEFX v p o) : epsSEFX v p eps o := by sorry
