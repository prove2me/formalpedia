-- Prove2me | Theorems.Thm_DeletionCode_SingleEditOrigins_Edit_clean_block
-- name    : DeletionCode.SingleEditOrigins.Edit.clean_block
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:29:19.393361+00:00
-- url     : https://prove2.me/theorems/403d86af-85f2-4c35-b909-0757c9fd2e4f
-- title:
--   Edit: clean block
-- statement:
--   A block lying wholly before or strictly after the cut consists of
--   consecutive original source positions. This also holds for an empty block.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditOrigins.lean#L109-L140
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditOrigins.lean#L109-L140

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_SingleEditOrigins
set_option autoImplicit true
open DeletionCode DeletionCode.SingleEditOrigins
open Windows
open DeletionCode.SingleEditOrigins.Edit

theorem DeletionCode.SingleEditOrigins.Edit.clean_block (e : Edit) (a s k : ℕ)
    (h : a + s + k ≤ e.cut ∨ e.cut < a + s) :
    ∃ r, ∀ i, i < k → e.origin (a + s + i) = some (r + i) := by sorry
