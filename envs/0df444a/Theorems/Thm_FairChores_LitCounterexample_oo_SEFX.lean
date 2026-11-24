-- Prove2me | Theorems.Thm_FairChores_LitCounterexample_oo_SEFX
-- name    : FairChores.LitCounterexample.oo_SEFX
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:22:38.241852+00:00
-- url     : https://prove2.me/theorems/a740321d-b837-4d49-9776-2f00c19ed70b
-- title:
--   Lit Counterexample: oo SEFX
-- statement:
--   ... and satisfies the corrected `SEFX`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresEnvy.lean#L243-L243
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresEnvy.lean#L243-L243

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
open FairChores.LitCounterexample

theorem FairChores.LitCounterexample.oo_SEFX : SEFX cc pp oo := by sorry
