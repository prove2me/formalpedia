-- Prove2me | Theorems.Thm_DeletionCode_SingleEditScripts_insert_split
-- name    : DeletionCode.SingleEditScripts.insert_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:21:37.474516+00:00
-- url     : https://prove2.me/theorems/9ff82acc-603e-43ab-9358-d833c3760c23
-- title:
--   Single Edit Scripts: insert split
-- statement:
--   Insertion semantics follow from the already verified inverse edit identity.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditScripts.lean#L65-L75
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditScripts.lean#L65-L75

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_SingleEditOrigins
import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SingleEditScripts
set_option autoImplicit true
open DeletionCode DeletionCode.SingleEditScripts
open Windows CatalogueWords EditAlignment SingleEditOrigins

theorem DeletionCode.SingleEditScripts.insert_split (pre suffix : List Bool) (bit : Bool) :
    insertAt (listLetters (pre ++ suffix)) pre.length bit =
      listLetters (pre ++ bit :: suffix) := by sorry
