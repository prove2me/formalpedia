-- Prove2me | Theorems.Thm_FairSelling_truncSum_mono
-- name    : FairSelling.truncSum_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:51:07.204691+00:00
-- url     : https://prove2.me/theorems/695f469a-0b94-4d3b-bc74-7604370ca691
-- title:
--   Fair Selling: trunc Sum mono
-- statement:
--   The Fair Selling construction uses the trunc Sum mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L363-L365
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Selling.lean#L363-L365

import Mathlib
import Definitions.Def_RequestProject_Selling
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [DecidableEq G]

theorem FairSelling.truncSum_mono (v p : G → ℝ) : Monotone (truncSum n v p) := by sorry
