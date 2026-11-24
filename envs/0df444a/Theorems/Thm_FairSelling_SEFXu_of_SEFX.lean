-- Prove2me | Theorems.Thm_FairSelling_SEFXu_of_SEFX
-- name    : FairSelling.SEFXu_of_SEFX
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:38:35.854713+00:00
-- url     : https://prove2.me/theorems/3b5c1cc5-f762-40f0-891b-36c1fd00ae11
-- title:
--   Fair Selling: SEFXu of SEFX
-- statement:
--   `SEFX` (Definition 4.2, corrected) implies its utility form, for a valid outcome.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L190-L204
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L190-L204

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}

theorem FairSelling.SEFXu_of_SEFX (hvalid : o.Valid p) (ho : SEFX v p o) : SEFXu v p o := by sorry
