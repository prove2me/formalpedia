-- Prove2me | Theorems.Thm_FairSelling_SEFXu_of_SEFXs
-- name    : FairSelling.SEFXu_of_SEFXs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:34:57.110806+00:00
-- url     : https://prove2.me/theorems/33e28402-383e-47a5-b7a2-d1da9b332651
-- title:
--   Fair Selling: SEFXu of SEFXs
-- statement:
--   The strong form implies the utility form, for a valid outcome.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L262-L263
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L262-L263

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}

theorem FairSelling.SEFXu_of_SEFXs (hvalid : o.Valid p) (ho : SEFXs v p o) : SEFXu v p o := by sorry
