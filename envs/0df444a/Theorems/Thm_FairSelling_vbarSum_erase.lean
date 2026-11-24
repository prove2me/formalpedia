-- Prove2me | Theorems.Thm_FairSelling_vbarSum_erase
-- name    : FairSelling.vbarSum_erase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:38:27.45586+00:00
-- url     : https://prove2.me/theorems/2329e458-d467-45d7-94ec-e7182ff4600b
-- title:
--   Fair Selling: vbar Sum erase
-- statement:
--   Splitting off one good from a bundle, measured with `v̄ᵢ`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L182-L184
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EpsEnvy.lean#L182-L184

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}

theorem FairSelling.vbarSum_erase {vi p : G → ℝ} {A : Finset G} {g : G} (hg : g ∈ A) :
    vbarSum vi p A = vbarSum vi p (A \ {g}) + vbar vi p g := by sorry
