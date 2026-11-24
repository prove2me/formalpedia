-- Prove2me | Theorems.Thm_FairSelling_SEF1_of_SEF1lit
-- name    : FairSelling.SEF1_of_SEF1lit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:27:57.307173+00:00
-- url     : https://prove2.me/theorems/fa7f08c4-880d-4c39-9279-81de73cc8727
-- title:
--   Fair Selling: SEF1 of SEF1lit
-- statement:
--   The literal reading of Definition 4.1 implies the corrected `SEF1`, for a valid outcome.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L230-L235
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L230-L235

import Mathlib
import Definitions.Def_RequestProject_Selling
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}
omit [Fintype G]

theorem FairSelling.SEF1_of_SEF1lit (hvalid : o.Valid p) (h : SEF1lit v p o) : SEF1 v p o := by sorry
