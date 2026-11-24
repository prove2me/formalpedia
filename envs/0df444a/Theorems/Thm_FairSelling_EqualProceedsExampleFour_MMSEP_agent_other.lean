-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsExampleFour_MMSEP_agent_other
-- name    : FairSelling.EqualProceedsExampleFour.MMSEP_agent_other
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:25:24.22627+00:00
-- url     : https://prove2.me/theorems/34b07d87-0474-4d36-ae23-6a23dcfe6bf5
-- title:
--   Equal Proceeds Example Four: MMSEP agent other
-- statement:
--   The Equal Proceeds Example Four construction uses the MMSEP agent other property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L300-L302
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L300-L302

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleFour
variable (N : ℕ)

theorem FairSelling.EqualProceedsExampleFour.MMSEP_agent_other (L : ℝ) (hL : 1 ≤ L) {i : Fin (N + 2)} (hi : i ≠ 0) :
    MMSEP (N + 2) (val N L i) (price N) = L := by sorry
