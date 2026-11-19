-- Prove2me | Theorems.Thm_DeletionCode_SingleEditScripts_delete_split
-- name    : DeletionCode.SingleEditScripts.delete_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:19:31.943635+00:00
-- url     : https://prove2.me/theorems/7da850e4-d844-410a-9e82-39512ea9ad58
-- title:
--   Single Edit Scripts: delete split
-- statement:
--   The Single Edit Scripts construction uses the delete split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditScripts.lean#L59-L62
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditScripts.lean#L59-L62

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_SingleEditOrigins
import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SingleEditScripts
set_option autoImplicit true
open DeletionCode DeletionCode.SingleEditScripts
open Windows CatalogueWords EditAlignment SingleEditOrigins

theorem DeletionCode.SingleEditScripts.delete_split (pre suffix : List Bool) (bit : Bool) :
    deleteAt (listLetters (pre ++ bit :: suffix)) pre.length =
      listLetters (pre ++ suffix) := by sorry
