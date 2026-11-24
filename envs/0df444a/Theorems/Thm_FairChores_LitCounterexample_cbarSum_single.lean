-- Prove2me | Theorems.Thm_FairChores_LitCounterexample_cbarSum_single
-- name    : FairChores.LitCounterexample.cbarSum_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:47:44.280917+00:00
-- url     : https://prove2.me/theorems/5737625a-04d6-4d12-8ec0-6a92e43af562
-- title:
--   Lit Counterexample: cbar Sum single
-- statement:
--   The Lit Counterexample construction uses the cbar Sum single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresEnvy.lean#L231-L232
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresEnvy.lean#L231-L232

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
open FairChores.LitCounterexample

theorem FairChores.LitCounterexample.cbarSum_single (i j : Fin 2) : cbarSum (cc i) pp {j} = 1 := by sorry
