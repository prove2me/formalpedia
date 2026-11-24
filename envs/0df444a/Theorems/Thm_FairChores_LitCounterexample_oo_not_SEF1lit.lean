-- Prove2me | Theorems.Thm_FairChores_LitCounterexample_oo_not_SEF1lit
-- name    : FairChores.LitCounterexample.oo_not_SEF1lit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:17:41.783038+00:00
-- url     : https://prove2.me/theorems/cd3540b4-f204-4116-a970-86467dc6d9b8
-- title:
--   Lit Counterexample: oo not SEF1lit
-- statement:
--   ... and it does not satisfy the literal `SEF1` either.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresEnvy.lean#L254-L258
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresEnvy.lean#L254-L258

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
open FairChores.LitCounterexample

theorem FairChores.LitCounterexample.oo_not_SEF1lit : ¬ SEF1lit cc pp oo := by sorry
