-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsExampleThree_out2_equalProceeds
-- name    : FairSelling.EqualProceedsExampleThree.out2_equalProceeds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:24:35.24151+00:00
-- url     : https://prove2.me/theorems/23fa2b72-facc-4e39-af35-6f1fd9ff2a9a
-- title:
--   Equal Proceeds Example Three: out2 equal Proceeds
-- statement:
--   The Equal Proceeds Example Three construction uses the out2 equal Proceeds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L136-L140
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L136-L140

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleThree
variable (N : ℕ)

theorem FairSelling.EqualProceedsExampleThree.out2_equalProceeds : (out2 N).EqualProceeds (price N) := by sorry
