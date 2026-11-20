-- Prove2me | Theorems.Thm_DeletionCode_AnchorRecords_exists_finite_record
-- name    : DeletionCode.AnchorRecords.exists_finite_record
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:55:22.444968+00:00
-- url     : https://prove2.me/theorems/7dfb1ac0-0b15-4b2e-a978-e6442af99f5f
-- title:
--   Anchor Records: exists finite record
-- statement:
--   Every positive balanced trace has a record in the finite product space
--   used in the counting proof. The packet list is equal to the actual encoding.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AnchorRecords.lean#L221-L231
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AnchorRecords.lean#L221-L231

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceSeparation
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_AnchorRecords
set_option autoImplicit true
open DeletionCode DeletionCode.AnchorRecords
open AlignmentTrace TraceEditData

theorem DeletionCode.AnchorRecords.exists_finite_record (trace : Trace) (n d : ℕ)
    (hsource : trace.source.length = n) (hdel : trace.deletions = d)
    (hins : trace.insertions = d) (hd : 1 ≤ d) :
    ∃ anchors : Fin (2 * d) → Fin n, ∃ data : Fin (2 * d) → Bool × Bool,
      List.ofFn (fun i => ((anchors i).val, data i)) = encode trace := by sorry
