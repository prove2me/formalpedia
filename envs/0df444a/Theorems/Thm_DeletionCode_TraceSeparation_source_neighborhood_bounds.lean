-- Prove2me | Theorems.Thm_DeletionCode_TraceSeparation_source_neighborhood_bounds
-- name    : DeletionCode.TraceSeparation.source_neighborhood_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:37:34.035269+00:00
-- url     : https://prove2.me/theorems/207b6329-d17f-44e6-a80f-caf27b4c2a24
-- title:
--   Trace Separation: source neighborhood bounds
-- statement:
--   The Trace Separation construction uses the source neighborhood bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L146-L151
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L146-L151

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph

theorem DeletionCode.TraceSeparation.source_neighborhood_bounds {trace : Trace} {L : ℕ} (hL : 1 ≤ L)
    (hsep : Separated (4 * L) trace) (i : Fin trace.length) (hi : EditIndex trace i) :
    neighborhoodLeft L (trace.sourcePosition i.val) + 2 * L =
        neighborhoodRight L (trace.sourcePosition i.val) ∧
      neighborhoodRight L (trace.sourcePosition i.val) ≤ trace.source.length := by sorry
