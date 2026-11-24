-- Prove2me | Theorems.Thm_FairChores_LitCounterexample_oo_not_SEFXlit
-- name    : FairChores.LitCounterexample.oo_not_SEFXlit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:17:17.000705+00:00
-- url     : https://prove2.me/theorems/9b2d23c0-cac8-42fb-8b6b-96e70a5cd589
-- title:
--   Lit Counterexample: oo not SEFXlit
-- statement:
--   ... but it does **not** satisfy the literal `SEFX`: the literal notion is therefore not a
--   relaxation of envy-freeness.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresEnvy.lean#L247-L251
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresEnvy.lean#L247-L251

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
open FairChores.LitCounterexample

theorem FairChores.LitCounterexample.oo_not_SEFXlit : ¬ SEFXlit cc pp oo := by sorry
