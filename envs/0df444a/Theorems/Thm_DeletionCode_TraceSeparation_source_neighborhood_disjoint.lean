-- Prove2me | Theorems.Thm_DeletionCode_TraceSeparation_source_neighborhood_disjoint
-- name    : DeletionCode.TraceSeparation.source_neighborhood_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:37:33.809317+00:00
-- url     : https://prove2.me/theorems/fd05f7d8-a6c7-41e5-8014-b00f3a2bc4b8
-- title:
--   Trace Separation: source neighborhood disjoint
-- statement:
--   Distinct edit columns have disjoint actual source neighborhoods.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L185-L194
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L185-L194

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph

theorem DeletionCode.TraceSeparation.source_neighborhood_disjoint {trace : Trace} {L : ℕ} (hL : 1 ≤ L)
    (hsep : Separated (4 * L) trace) (i j : Fin trace.length)
    (hi : EditIndex trace i) (hj : EditIndex trace j) (hne : i ≠ j) :
    Disjoint (neighborhood L (trace.sourcePosition i.val))
      (neighborhood L (trace.sourcePosition j.val)) := by sorry
