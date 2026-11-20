-- Prove2me | Theorems.Thm_DeletionCode_TraceSeparation_neighborhood_subset
-- name    : DeletionCode.TraceSeparation.neighborhood_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:37:09.088172+00:00
-- url     : https://prove2.me/theorems/0f9b7546-68f2-4e8f-a2da-8c7811e6a3b0
-- title:
--   Trace Separation: neighborhood subset
-- statement:
--   The Trace Separation construction uses the neighborhood subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L124-L129
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L124-L129

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph

theorem DeletionCode.TraceSeparation.neighborhood_subset {L position n : ℕ} (hL : 1 ≤ L)
    (hmargins : 4 * L ≤ position ∧ position + 4 * L ≤ n) :
    neighborhood L position ⊆ Set.Ico 0 n := by sorry
