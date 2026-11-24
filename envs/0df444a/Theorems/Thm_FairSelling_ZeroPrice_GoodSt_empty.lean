-- Prove2me | Theorems.Thm_FairSelling_ZeroPrice_GoodSt_empty
-- name    : FairSelling.ZeroPrice.GoodSt_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:55:15.719565+00:00
-- url     : https://prove2.me/theorems/315635ab-3691-4341-88d6-3b90e8f5b3c0
-- title:
--   Zero Price: Good St empty
-- statement:
--   The empty state is legitimate.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxZero.lean#L97-L101
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxZero.lean#L97-L101

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxZero
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ZeroPrice
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.ZeroPrice.GoodSt_empty (v : Fin n → G → ℝ) (p : G → ℝ) :
    GoodSt v p ((∅ : Finset (Fin n)), fun _ => (∅ : Finset G)) := by sorry
