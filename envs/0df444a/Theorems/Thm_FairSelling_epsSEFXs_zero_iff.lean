-- Prove2me | Theorems.Thm_FairSelling_epsSEFXs_zero_iff
-- name    : FairSelling.epsSEFXs_zero_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:34:36.410056+00:00
-- url     : https://prove2.me/theorems/a675e436-51b0-4dfb-96a0-5922b2c9366a
-- title:
--   Fair Selling: eps SEFXs zero iff
-- statement:
--   The Fair Selling construction uses the eps SEFXs zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L240-L242
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L240-L242

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}

theorem FairSelling.epsSEFXs_zero_iff : epsSEFXs v p 0 o ↔ SEFXs v p o := by sorry
