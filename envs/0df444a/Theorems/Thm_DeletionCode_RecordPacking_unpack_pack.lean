-- Prove2me | Theorems.Thm_DeletionCode_RecordPacking_unpack_pack
-- name    : DeletionCode.RecordPacking.unpack_pack
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:15:18.379419+00:00
-- url     : https://prove2.me/theorems/1c37a23e-da6e-4ecc-89aa-035a5ab01f30
-- title:
--   Record Packing: unpack pack
-- statement:
--   The Record Packing construction uses the unpack pack property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RecordPacking.lean#L47-L59
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RecordPacking.lean#L47-L59

import Mathlib.Data.List.OfFn
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_RecordPacking
set_option autoImplicit true
open DeletionCode DeletionCode.RecordPacking
variable {α β : Type*}

theorem DeletionCode.RecordPacking.unpack_pack (decode : β → Option (Option α)) (encode : α → β)
    (padding : β) (hpadding : decode padding = some none)
    (xs : List α) (hencode : ∀ a ∈ xs, decode (encode a) = some (some a))
    (size : ℕ) (hsize : xs.length ≤ size) :
    unpack decode size (pack padding (xs.map encode) size) = some xs := by sorry
