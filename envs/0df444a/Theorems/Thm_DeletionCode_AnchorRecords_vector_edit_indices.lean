-- Prove2me | Theorems.Thm_DeletionCode_AnchorRecords_vector_edit_indices
-- name    : DeletionCode.AnchorRecords.vector_edit_indices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:55:26.166481+00:00
-- url     : https://prove2.me/theorems/7f72482c-e60f-4693-8fbc-2acd4ec9d83f
-- title:
--   Anchor Records: vector edit indices
-- statement:
--   Any finite-vector presentation of the encoding contains distinct indices
--   for distinct actual edits, with precisely their matched-column anchors.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AnchorRecords.lean#L235-L255
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AnchorRecords.lean#L235-L255

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceSeparation
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_AnchorRecords
set_option autoImplicit true
open DeletionCode DeletionCode.AnchorRecords
open AlignmentTrace TraceEditData

theorem DeletionCode.AnchorRecords.vector_edit_indices (trace : Trace) {n r : ℕ}
    (anchors : Fin r → Fin n) (data : Fin r → Bool × Bool)
    (heq : List.ofFn (fun i => ((anchors i).val, data i)) = encode trace) :
    ∃ e : EditColumn trace → Fin r, Function.Injective e ∧
      ∀ c, (anchors (e c)).val = trace.matchedAnchor c.val.val := by sorry
