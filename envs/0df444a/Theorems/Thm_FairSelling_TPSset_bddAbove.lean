-- Prove2me | Theorems.Thm_FairSelling_TPSset_bddAbove
-- name    : FairSelling.TPSset_bddAbove
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:25:02.770781+00:00
-- url     : https://prove2.me/theorems/5f02bc39-4544-44e9-8a0b-5386b68153e9
-- title:
--   Fair Selling: TPSset bdd Above
-- statement:
--   The Fair Selling construction uses the TPSset bdd Above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L276-L277
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L276-L277

import Mathlib
import Definitions.Def_RequestProject_Selling
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [DecidableEq G]

theorem FairSelling.TPSset_bddAbove (v p : G → ℝ) :
    BddAbove (TPSset n v p) := by sorry
