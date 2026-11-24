-- Prove2me | Theorems.Thm_FairSelling_epsSEFX_zero_iff
-- name    : FairSelling.epsSEFX_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:38:25.692319+00:00
-- url     : https://prove2.me/theorems/b7a7622f-af51-4914-9c90-409f29f7b071
-- title:
--   Fair Selling: eps SEFX zero iff
-- statement:
--   At `ε = 0`, Definition 8.2 is Definition 4.2.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L110-L112
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L110-L112

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}

theorem FairSelling.epsSEFX_zero_iff : epsSEFX v p 0 o ↔ SEFX v p o := by sorry
