-- Prove2me | Theorems.Thm_FairSelling_epsSEFX_mono
-- name    : FairSelling.epsSEFX_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:53:14.065875+00:00
-- url     : https://prove2.me/theorems/ea221cc9-82fd-47b2-91a2-cfdd1dcfb794
-- title:
--   Fair Selling: eps SEFX mono
-- statement:
--   `ε-SEFX` is monotone in `ε`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L125-L131
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L125-L131

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}

theorem FairSelling.epsSEFX_mono {eps eps' : ℝ} (h : eps ≤ eps') (ho : epsSEFX v p eps o) :
    epsSEFX v p eps' o := by sorry
