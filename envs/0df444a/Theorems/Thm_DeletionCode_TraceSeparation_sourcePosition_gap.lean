-- Prove2me | Theorems.Thm_DeletionCode_TraceSeparation_sourcePosition_gap
-- name    : DeletionCode.TraceSeparation.sourcePosition_gap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:36:52.407423+00:00
-- url     : https://prove2.me/theorems/cd807c0a-bc32-487a-92e7-405c71290f6e
-- title:
--   Trace Separation: source Position gap
-- statement:
--   An anchor gap remains at least as large in source coordinates.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L43-L49
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L43-L49

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph

theorem DeletionCode.TraceSeparation.sourcePosition_gap (trace : Trace) {i j B : ℕ} (hij : i ≤ j)
    (hgap : trace.matchedAnchor i + B ≤ trace.matchedAnchor j) :
    trace.sourcePosition i + B ≤ trace.sourcePosition j := by sorry
