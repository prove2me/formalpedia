-- Prove2me | Theorems.Thm_DeletionCode_SingleEditScripts_listLetters_at_split
-- name    : DeletionCode.SingleEditScripts.listLetters_at_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:21:32.919743+00:00
-- url     : https://prove2.me/theorems/87145bb1-40d3-446e-accb-502aa18577cd
-- title:
--   Single Edit Scripts: list Letters at split
-- statement:
--   The actual bit at a list split is the inserted/deleted bit.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditScripts.lean#L53-L57
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditScripts.lean#L53-L57

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_SingleEditOrigins
import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SingleEditScripts
set_option autoImplicit true
open DeletionCode DeletionCode.SingleEditScripts
open Windows CatalogueWords EditAlignment SingleEditOrigins

theorem DeletionCode.SingleEditScripts.listLetters_at_split (pre suffix : List Bool) (bit : Bool) :
    listLetters (pre ++ bit :: suffix) pre.length = bit := by sorry
