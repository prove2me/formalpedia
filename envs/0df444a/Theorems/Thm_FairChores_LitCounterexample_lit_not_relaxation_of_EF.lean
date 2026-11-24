-- Prove2me | Theorems.Thm_FairChores_LitCounterexample_lit_not_relaxation_of_EF
-- name    : FairChores.LitCounterexample.lit_not_relaxation_of_EF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:22:54.739964+00:00
-- url     : https://prove2.me/theorems/1867a91a-1fcd-4e21-b869-19a961ef7732
-- title:
--   Lit Counterexample: lit not relaxation of EF
-- statement:
--   Summary: there is a valid, fully envy-free chores allocation that satisfies neither the
--   literal `SEF1` nor the literal `SEFX` of Definition 9.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresEnvy.lean#L262-L265
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresEnvy.lean#L262-L265

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
open FairChores.LitCounterexample

theorem FairChores.LitCounterexample.lit_not_relaxation_of_EF :
    ∃ (c : Fin 2 → Fin 2 → ℝ) (p : Fin 2 → ℝ) (o : Outcome (Fin 2) 2),
      o.Valid p ∧ EF c p o ∧ ¬ SEF1lit c p o ∧ ¬ SEFXlit c p o := by sorry
