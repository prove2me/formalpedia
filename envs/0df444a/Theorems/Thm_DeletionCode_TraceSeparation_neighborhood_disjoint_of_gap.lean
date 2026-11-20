-- Prove2me | Theorems.Thm_DeletionCode_TraceSeparation_neighborhood_disjoint_of_gap
-- name    : DeletionCode.TraceSeparation.neighborhood_disjoint_of_gap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:36:46.852796+00:00
-- url     : https://prove2.me/theorems/560a71a3-3b3d-4283-afce-445c36f36fa2
-- title:
--   Trace Separation: neighborhood disjoint of gap
-- statement:
--   The Trace Separation construction uses the neighborhood disjoint of gap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L137-L144
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L137-L144

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph

theorem DeletionCode.TraceSeparation.neighborhood_disjoint_of_gap {L a b : ℕ} (hL : 1 ≤ L)
    (hgap : a + 4 * L ≤ b) : Disjoint (neighborhood L a) (neighborhood L b) := by sorry
