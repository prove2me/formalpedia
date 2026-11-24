-- Prove2me | Theorems.Thm_FairSelling_vval_mem_breakpoints
-- name    : FairSelling.vval_mem_breakpoints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:38:18.952814+00:00
-- url     : https://prove2.me/theorems/39159783-8257-4f2d-b43a-623e12cbc338
-- title:
--   Fair Selling: vval mem breakpoints
-- statement:
--   The Fair Selling construction uses the vval mem breakpoints property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSCompute.lean#L341-L344
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSCompute.lean#L341-L344

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TPSCompute
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]

theorem FairSelling.vval_mem_breakpoints (v p : G → ℝ) (g : G) : v g ∈ breakpoints v p := by sorry
