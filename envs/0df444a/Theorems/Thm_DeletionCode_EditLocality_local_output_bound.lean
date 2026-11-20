-- Prove2me | Theorems.Thm_DeletionCode_EditLocality_local_output_bound
-- name    : DeletionCode.EditLocality.local_output_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:39:14.390649+00:00
-- url     : https://prove2.me/theorems/70323a6e-ed06-4b90-b46e-38cd662f6dca
-- title:
--   Edit Locality: local output bound
-- statement:
--   The Edit Locality construction uses the local output bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/EditLocality.lean#L23-L26
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/EditLocality.lean#L23-L26

import Definitions.Def_DeletionCode_EditRigidity
import Mathlib.Order.Interval.Set.Basic
import Definitions.Def_DeletionCode_EditLocality
set_option autoImplicit true
open DeletionCode DeletionCode.EditLocality
open Windows HeaderRecovery SingleEditOrigins

theorem DeletionCode.EditLocality.local_output_bound (e : Edit) (start len n : ℕ)
    (he : Inside e start len) (hbound : start + len ≤ n) :
    start + e.outputLength len ≤ e.outputLength n := by sorry
