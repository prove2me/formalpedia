-- Prove2me | Theorems.Thm_FairSelling_mem_MMSEPset_zero
-- name    : FairSelling.mem_MMSEPset_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:48:49.829936+00:00
-- url     : https://prove2.me/theorems/98b01664-7d2b-4772-83a9-506a0a88bdd4
-- title:
--   Fair Selling: mem MMSEPset zero
-- statement:
--   The Fair Selling construction uses the mem MMSEPset zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceeds.lean#L49-L51
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceeds.lean#L49-L51

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EqualProceeds
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G] [DecidableEq G]

theorem FairSelling.mem_MMSEPset_zero (v p : G → ℝ) : (0 : ℝ) ∈ MMSEPset n v p := by sorry
