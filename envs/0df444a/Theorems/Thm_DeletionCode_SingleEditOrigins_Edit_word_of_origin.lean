-- Prove2me | Theorems.Thm_DeletionCode_SingleEditOrigins_Edit_word_of_origin
-- name    : DeletionCode.SingleEditOrigins.Edit.word_of_origin
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:28:59.704069+00:00
-- url     : https://prove2.me/theorems/fdb7b67c-a145-49ee-a2b1-a5e00c0976ae
-- title:
--   Edit: word of origin
-- statement:
--   A source-labelled output bit is precisely the bit at that source position.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditOrigins.lean#L54-L74
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditOrigins.lean#L54-L74

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_SingleEditOrigins
set_option autoImplicit true
open DeletionCode DeletionCode.SingleEditOrigins
open Windows
open DeletionCode.SingleEditOrigins.Edit

theorem DeletionCode.SingleEditOrigins.Edit.word_of_origin (e : Edit) (x : Letters) {i r : ℕ}
    (h : e.origin i = some r) : e.word x i = x r := by sorry
