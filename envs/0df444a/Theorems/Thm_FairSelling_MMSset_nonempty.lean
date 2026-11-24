-- Prove2me | Theorems.Thm_FairSelling_MMSset_nonempty
-- name    : FairSelling.MMSset_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:30:00.933848+00:00
-- url     : https://prove2.me/theorems/856beb16-53e5-4cae-b170-72be801d44b1
-- title:
--   Fair Selling: MMSset nonempty
-- statement:
--   The Fair Selling construction uses the MMSset nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L252-L253
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L252-L253

import Mathlib
import Definitions.Def_RequestProject_Selling
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [Fintype G] [DecidableEq G]

theorem FairSelling.MMSset_nonempty (v p : G → ℝ) :
    (MMSset n v p).Nonempty := by sorry
