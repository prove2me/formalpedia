-- Prove2me | Theorems.Thm_DeletionCode_AnchorRecords_finite_record_of_bounds
-- name    : DeletionCode.AnchorRecords.finite_record_of_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:55:09.305573+00:00
-- url     : https://prove2.me/theorems/0a5c0d03-198b-4ee3-9d98-b3eb899159cc
-- title:
--   Anchor Records: finite record of bounds
-- statement:
--   The Anchor Records construction uses the finite record of bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AnchorRecords.lean#L208-L217
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AnchorRecords.lean#L208-L217

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceSeparation
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_AnchorRecords
set_option autoImplicit true
open DeletionCode DeletionCode.AnchorRecords
open AlignmentTrace TraceEditData

theorem DeletionCode.AnchorRecords.finite_record_of_bounds (packets : List Packet) (n r : ℕ)
    (hlen : packets.length = r) (hbound : ∀ p ∈ packets, p.1 < n) :
    ∃ anchors : Fin r → Fin n, ∃ data : Fin r → Bool × Bool,
      List.ofFn (fun i => ((anchors i).val, data i)) = packets := by sorry
