-- Prove2me | Theorems.Thm_FairSelling_epsSEF1_mono
-- name    : FairSelling.epsSEF1_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:33:45.099779+00:00
-- url     : https://prove2.me/theorems/c62ed12b-b93a-4ff9-87be-4779736f0da6
-- title:
--   Fair Selling: eps SEF1 mono
-- statement:
--   `ε-SEF1` is monotone in `ε`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L134-L140
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L134-L140

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}

theorem FairSelling.epsSEF1_mono {eps eps' : ℝ} (h : eps ≤ eps') (ho : epsSEF1 v p eps o) :
    epsSEF1 v p eps' o := by sorry
