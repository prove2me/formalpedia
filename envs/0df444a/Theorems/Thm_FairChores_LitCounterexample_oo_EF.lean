-- Prove2me | Theorems.Thm_FairChores_LitCounterexample_oo_EF
-- name    : FairChores.LitCounterexample.oo_EF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:47:49.563805+00:00
-- url     : https://prove2.me/theorems/d3a32649-a1ff-4c9b-97c5-95d7efa1835e
-- title:
--   Lit Counterexample: oo EF
-- statement:
--   The allocation is envy free.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresEnvy.lean#L238-L240
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresEnvy.lean#L238-L240

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
open FairChores.LitCounterexample

theorem FairChores.LitCounterexample.oo_EF : EF cc pp oo := by sorry
