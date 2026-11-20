-- Prove2me | Theorems.Thm_DeletionCode_TraceSeparation_sourcePosition_separated
-- name    : DeletionCode.TraceSeparation.sourcePosition_separated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:36:28.412504+00:00
-- url     : https://prove2.me/theorems/62146151-bd11-4c13-a57d-add482581074
-- title:
--   Trace Separation: source Position separated
-- statement:
--   The source positions of any ordered pair of edits retain the full gap B.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L95-L99
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L95-L99

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph

theorem DeletionCode.TraceSeparation.sourcePosition_separated {trace : Trace} {B : ℕ}
    (hsep : Separated B trace) (i j : Fin trace.length)
    (hi : EditIndex trace i) (hj : EditIndex trace j) (hij : i.val < j.val) :
    trace.sourcePosition i.val + B ≤ trace.sourcePosition j.val := by sorry
