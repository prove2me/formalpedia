-- Prove2me | Theorems.Thm_FairChores_LitCounterexample_cbarSum_kept
-- name    : FairChores.LitCounterexample.cbarSum_kept
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:47:46.979288+00:00
-- url     : https://prove2.me/theorems/6c4a8a3a-7663-4e94-8b95-4fc6c59645ca
-- title:
--   Lit Counterexample: cbar Sum kept
-- statement:
--   The Lit Counterexample construction uses the cbar Sum kept property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresEnvy.lean#L234-L235
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresEnvy.lean#L234-L235

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
open FairChores.LitCounterexample

theorem FairChores.LitCounterexample.cbarSum_kept (i j : Fin 2) : cbarSum (cc i) pp (oo.kept j) = 1 := by sorry
