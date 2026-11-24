-- Prove2me | Theorems.Thm_FairSelling_epsSEFXlit_zero_iff
-- name    : FairSelling.epsSEFXlit_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:33:21.874799+00:00
-- url     : https://prove2.me/theorems/4f77de1f-60c8-4bf9-8beb-40e7945a1799
-- title:
--   Fair Selling: eps SEFXlit zero iff
-- statement:
--   At `ε = 0`, the literal Definition 8.2 is the literal Definition 4.2.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L120-L122
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L120-L122

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}

theorem FairSelling.epsSEFXlit_zero_iff : epsSEFXlit v p 0 o ↔ SEFXlit v p o := by sorry
