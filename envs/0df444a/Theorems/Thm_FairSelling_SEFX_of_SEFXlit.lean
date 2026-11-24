-- Prove2me | Theorems.Thm_FairSelling_SEFX_of_SEFXlit
-- name    : FairSelling.SEFX_of_SEFXlit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:27:51.666245+00:00
-- url     : https://prove2.me/theorems/260deae4-e385-4d74-b5cc-aced7694dc27
-- title:
--   Fair Selling: SEFX of SEFXlit
-- statement:
--   The literal reading of Definition 4.2 implies the corrected `SEFX`, for a valid outcome.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L221-L226
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L221-L226

import Mathlib
import Definitions.Def_RequestProject_Selling
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}
omit [Fintype G]

theorem FairSelling.SEFX_of_SEFXlit (hvalid : o.Valid p) (h : SEFXlit v p o) : SEFX v p o := by sorry
