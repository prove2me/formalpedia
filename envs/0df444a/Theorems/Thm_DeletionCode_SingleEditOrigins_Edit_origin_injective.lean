-- Prove2me | Theorems.Thm_DeletionCode_SingleEditOrigins_Edit_origin_injective
-- name    : DeletionCode.SingleEditOrigins.Edit.origin_injective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:29:14.242911+00:00
-- url     : https://prove2.me/theorems/f2a1f061-ce50-4c6d-84ae-303bc46d1bb8
-- title:
--   Edit: origin injective
-- statement:
--   No original source position survives at two distinct output positions.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditOrigins.lean#L77-L88
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditOrigins.lean#L77-L88

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_SingleEditOrigins
set_option autoImplicit true
open DeletionCode DeletionCode.SingleEditOrigins
open Windows
open DeletionCode.SingleEditOrigins.Edit

theorem DeletionCode.SingleEditOrigins.Edit.origin_injective (e : Edit) {i j r : ℕ}
    (hi : e.origin i = some r) (hj : e.origin j = some r) : i = j := by sorry
