-- Prove2me | Theorems.Thm_DeletionCode_TraceSeparation_targetPosition_gap
-- name    : DeletionCode.TraceSeparation.targetPosition_gap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:37:11.891915+00:00
-- url     : https://prove2.me/theorems/583150b5-4d81-4505-9d61-862bb524fafe
-- title:
--   Trace Separation: target Position gap
-- statement:
--   An anchor gap remains at least as large in target coordinates.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L52-L58
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L52-L58

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph

theorem DeletionCode.TraceSeparation.targetPosition_gap (trace : Trace) {i j B : ℕ} (hij : i ≤ j)
    (hgap : trace.matchedAnchor i + B ≤ trace.matchedAnchor j) :
    trace.targetPosition i + B ≤ trace.targetPosition j := by sorry
