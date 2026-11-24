-- Prove2me | Theorems.Thm_FairSelling_epsSEF1_zero_iff
-- name    : FairSelling.epsSEF1_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:32:43.904142+00:00
-- url     : https://prove2.me/theorems/51763ed1-ac25-424f-bb3e-f376f105eb3d
-- title:
--   Fair Selling: eps SEF1 zero iff
-- statement:
--   At `ε = 0`, Definition 8.1 is Definition 4.1.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L105-L107
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L105-L107

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}

theorem FairSelling.epsSEF1_zero_iff : epsSEF1 v p 0 o ↔ SEF1 v p o := by sorry
