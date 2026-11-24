-- Prove2me | Theorems.Thm_FairSelling_epsSEFXu_of_epsSEFX
-- name    : FairSelling.epsSEFXu_of_epsSEFX
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:53:29.1683+00:00
-- url     : https://prove2.me/theorems/df7ba180-732d-4e23-8465-34100fe470c8
-- title:
--   Fair Selling: eps SEFXu of eps SEFX
-- statement:
--   `ε-SEFX` (Definition 8.2) implies the utility form `ε-SEFXu`, for a valid outcome:
--   this is the (only) step where the two notions of Definition 4/8 and their utility forms are
--   compared, and it is what makes the corrected Lemma 11 applicable to the manuscript's notion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L268-L282
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L268-L282

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}

theorem FairSelling.epsSEFXu_of_epsSEFX {eps : ℝ} (heps : 0 ≤ eps) (hvalid : o.Valid p)
    (ho : epsSEFX v p eps o) : epsSEFXu v p eps o := by sorry
