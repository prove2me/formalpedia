-- Prove2me | Theorems.Thm_FairSelling_epsSEF1lit_zero_iff
-- name    : FairSelling.epsSEF1lit_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:33:10.802616+00:00
-- url     : https://prove2.me/theorems/93d33e09-82ce-4f10-8c80-8b5696b6d345
-- title:
--   Fair Selling: eps SEF1lit zero iff
-- statement:
--   At `ε = 0`, the literal Definition 8.1 is the literal Definition 4.1.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L115-L117
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L115-L117

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}

theorem FairSelling.epsSEF1lit_zero_iff : epsSEF1lit v p 0 o ↔ SEF1lit v p o := by sorry
