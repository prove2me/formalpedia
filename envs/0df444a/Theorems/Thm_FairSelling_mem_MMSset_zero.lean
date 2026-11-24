-- Prove2me | Theorems.Thm_FairSelling_mem_MMSset_zero
-- name    : FairSelling.mem_MMSset_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:37:23.726521+00:00
-- url     : https://prove2.me/theorems/f90efd2c-53d4-46bd-a44e-3d27d78e3229
-- title:
--   Fair Selling: mem MMSset zero
-- statement:
--   The Fair Selling construction uses the mem MMSset zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L245-L249
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L245-L249

import Mathlib
import Definitions.Def_RequestProject_Selling
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [Fintype G] [DecidableEq G]

theorem FairSelling.mem_MMSset_zero (v p : G → ℝ) :
    (0 : ℝ) ∈ MMSset n v p := by sorry
