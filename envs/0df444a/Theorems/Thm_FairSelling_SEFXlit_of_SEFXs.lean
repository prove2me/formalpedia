-- Prove2me | Theorems.Thm_FairSelling_SEFXlit_of_SEFXs
-- name    : FairSelling.SEFXlit_of_SEFXs
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:34:57.02143+00:00
-- url     : https://prove2.me/theorems/2a2f0ea4-f662-4bad-81d3-88db5dac66f1
-- title:
--   Fair Selling: SEFXlit of SEFXs
-- statement:
--   The strong form implies the literal `SEFX` (Definition 4.2 as written).
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L254-L259
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L254-L259

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}

theorem FairSelling.SEFXlit_of_SEFXs (ho : SEFXs v p o) : SEFXlit v p o := by sorry
