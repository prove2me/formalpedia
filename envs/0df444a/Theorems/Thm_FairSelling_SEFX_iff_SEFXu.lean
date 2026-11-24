-- Prove2me | Theorems.Thm_FairSelling_SEFX_iff_SEFXu
-- name    : FairSelling.SEFX_iff_SEFXu
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:34:31.350421+00:00
-- url     : https://prove2.me/theorems/61311d5f-fc2e-4481-b791-73c993820509
-- title:
--   Fair Selling: SEFX iff SEFXu
-- statement:
--   `SEFX` (corrected) and its utility form coincide, for a valid outcome.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L216-L217
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L216-L217

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}

theorem FairSelling.SEFX_iff_SEFXu (hvalid : o.Valid p) : SEFX v p o ↔ SEFXu v p o := by sorry
