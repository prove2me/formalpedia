-- Prove2me | Theorems.Thm_DeletionCode_TraceSeparation_targetPosition_margins
-- name    : DeletionCode.TraceSeparation.targetPosition_margins
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:37:09.137795+00:00
-- url     : https://prove2.me/theorems/eb924480-2be7-4dbc-824f-d843bbbdb686
-- title:
--   Trace Separation: target Position margins
-- statement:
--   Every separated edit has the stated margin at both target boundaries.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L84-L92
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L84-L92

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph

theorem DeletionCode.TraceSeparation.targetPosition_margins {trace : Trace} {B : ℕ}
    (hsep : Separated B trace) (i : Fin trace.length) (hi : EditIndex trace i) :
    B ≤ trace.targetPosition i.val ∧
      trace.targetPosition i.val + B ≤ trace.target.length := by sorry
