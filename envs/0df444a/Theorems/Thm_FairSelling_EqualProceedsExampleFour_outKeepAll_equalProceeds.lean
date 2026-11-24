-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsExampleFour_outKeepAll_equalProceeds
-- name    : FairSelling.EqualProceedsExampleFour.outKeepAll_equalProceeds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:25:23.693639+00:00
-- url     : https://prove2.me/theorems/7a4c8502-ae61-48a3-a781-644bed620ef4
-- title:
--   Equal Proceeds Example Four: out Keep All equal Proceeds
-- statement:
--   The Equal Proceeds Example Four construction uses the out Keep All equal Proceeds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L257-L259
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L257-L259

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleFour
variable (N : ℕ)

theorem FairSelling.EqualProceedsExampleFour.outKeepAll_equalProceeds : (outKeepAll N).EqualProceeds (price N) := by sorry
