-- Prove2me | Theorems.Thm_DeletionCode_SingleEditOrigins_Edit_origin_lt
-- name    : DeletionCode.SingleEditOrigins.Edit.origin_lt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:29:13.215504+00:00
-- url     : https://prove2.me/theorems/37a8c39c-01e0-48e5-914a-54a5342ab334
-- title:
--   Edit: origin lt
-- statement:
--   Every surviving bit inside the valid output has an in-bounds source label.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditOrigins.lean#L91-L105
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditOrigins.lean#L91-L105

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_SingleEditOrigins
set_option autoImplicit true
open DeletionCode DeletionCode.SingleEditOrigins
open Windows
open DeletionCode.SingleEditOrigins.Edit

theorem DeletionCode.SingleEditOrigins.Edit.origin_lt (e : Edit) {n i r : ℕ} (hv : e.Valid n)
    (hi : i < e.outputLength n) (hr : e.origin i = some r) : r < n := by sorry
