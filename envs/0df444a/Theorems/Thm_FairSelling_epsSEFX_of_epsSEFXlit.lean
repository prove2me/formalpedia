-- Prove2me | Theorems.Thm_FairSelling_epsSEFX_of_epsSEFXlit
-- name    : FairSelling.epsSEFX_of_epsSEFXlit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:34:00.228271+00:00
-- url     : https://prove2.me/theorems/f493df0d-ace5-4756-ad82-c445fa353240
-- title:
--   Fair Selling: eps SEFX of eps SEFXlit
-- statement:
--   The literal `ε-SEFX` implies the corrected `ε-SEFX`, for a valid outcome.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L143-L149
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L143-L149

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}

theorem FairSelling.epsSEFX_of_epsSEFXlit {eps : ℝ} (hvalid : o.Valid p) (ho : epsSEFXlit v p eps o) :
    epsSEFX v p eps o := by sorry
