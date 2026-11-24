-- Prove2me | Theorems.Thm_FairSelling_epsSEFXu_zero_iff
-- name    : FairSelling.epsSEFXu_zero_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:34:24.456706+00:00
-- url     : https://prove2.me/theorems/9b11c336-7d17-41dc-9a24-f5ec0e4f905f
-- title:
--   Fair Selling: eps SEFXu zero iff
-- statement:
--   The Fair Selling construction uses the eps SEFXu zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L177-L179
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L177-L179

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}

theorem FairSelling.epsSEFXu_zero_iff : epsSEFXu v p 0 o ↔ SEFXu v p o := by sorry
