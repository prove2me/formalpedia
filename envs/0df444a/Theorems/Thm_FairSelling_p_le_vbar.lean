-- Prove2me | Theorems.Thm_FairSelling_p_le_vbar
-- name    : FairSelling.p_le_vbar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:38:29.954726+00:00
-- url     : https://prove2.me/theorems/c0f11693-93e5-48d2-902a-929404e51fc0
-- title:
--   Fair Selling: p le vbar
-- statement:
--   The Fair Selling construction uses the p le vbar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L187-L187
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L187-L187

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}
omit [DecidableEq G]

theorem FairSelling.p_le_vbar {vi p : G → ℝ} (g : G) : p g ≤ vbar vi p g := by sorry
