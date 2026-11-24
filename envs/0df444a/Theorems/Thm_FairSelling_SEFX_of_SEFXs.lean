-- Prove2me | Theorems.Thm_FairSelling_SEFX_of_SEFXs
-- name    : FairSelling.SEFX_of_SEFXs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:30:33.031838+00:00
-- url     : https://prove2.me/theorems/ceee6d3f-2c89-4cb9-a6f2-8b3dde5f5b32
-- title:
--   Fair Selling: SEFX of SEFXs
-- statement:
--   The strong form implies `SEFX` (Definition 4.2), for a valid outcome.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L245-L251
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L245-L251

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}

theorem FairSelling.SEFX_of_SEFXs (hvalid : o.Valid p) (ho : SEFXs v p o) : SEFX v p o := by sorry
