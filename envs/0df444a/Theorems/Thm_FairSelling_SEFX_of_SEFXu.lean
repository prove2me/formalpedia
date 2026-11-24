-- Prove2me | Theorems.Thm_FairSelling_SEFX_of_SEFXu
-- name    : FairSelling.SEFX_of_SEFXu
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:30:35.313799+00:00
-- url     : https://prove2.me/theorems/dd9215a8-2221-4dde-8bcb-5556aecd17ec
-- title:
--   Fair Selling: SEFX of SEFXu
-- statement:
--   Conversely, the utility form implies `SEFX` (Definition 4.2, corrected): the two notions
--   are in fact equivalent, which is what makes Lemma 11 go through for the corrected notion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L208-L213
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L208-L213

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}

theorem FairSelling.SEFX_of_SEFXu (ho : SEFXu v p o) : SEFX v p o := by sorry
