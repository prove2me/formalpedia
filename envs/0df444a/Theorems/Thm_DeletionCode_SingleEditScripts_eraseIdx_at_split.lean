-- Prove2me | Theorems.Thm_DeletionCode_SingleEditScripts_eraseIdx_at_split
-- name    : DeletionCode.SingleEditScripts.eraseIdx_at_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:21:21.572807+00:00
-- url     : https://prove2.me/theorems/3813a7e6-de9a-41d6-85d7-e18842f23597
-- title:
--   Single Edit Scripts: erase Idx at split
-- statement:
--   The Single Edit Scripts construction uses the erase Idx at split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditScripts.lean#L47-L50
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditScripts.lean#L47-L50

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_SingleEditOrigins
import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SingleEditScripts
set_option autoImplicit true
open DeletionCode DeletionCode.SingleEditScripts
open Windows CatalogueWords EditAlignment SingleEditOrigins

theorem DeletionCode.SingleEditScripts.eraseIdx_at_split (pre suffix : List Bool) (bit : Bool) :
    (pre ++ bit :: suffix).eraseIdx pre.length = pre ++ suffix := by sorry
