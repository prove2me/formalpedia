-- Prove2me | Theorems.Thm_DeletionCode_TraceSeparation_sourcePosition_margins
-- name    : DeletionCode.TraceSeparation.sourcePosition_margins
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:36:40.540905+00:00
-- url     : https://prove2.me/theorems/8082f0e0-11e6-46bf-8e9b-533d335400a0
-- title:
--   Trace Separation: source Position margins
-- statement:
--   Every separated edit has the stated margin at both source boundaries.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L73-L81
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L73-L81

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph

theorem DeletionCode.TraceSeparation.sourcePosition_margins {trace : Trace} {B : ℕ}
    (hsep : Separated B trace) (i : Fin trace.length) (hi : EditIndex trace i) :
    B ≤ trace.sourcePosition i.val ∧
      trace.sourcePosition i.val + B ≤ trace.source.length := by sorry
