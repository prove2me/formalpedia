-- Prove2me | Theorems.Thm_DeletionCode_SingleEditScripts_within_one_realized
-- name    : DeletionCode.SingleEditScripts.within_one_realized
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:20:08.750594+00:00
-- url     : https://prove2.me/theorems/1e84cf96-6151-4a1f-b415-d19ffa1a18b0
-- title:
--   Single Edit Scripts: within one realized
-- statement:
--   Every genuine script of cost at most one has a valid concrete edit realization.
--   The output length and complete padded word are both derived from the script.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditScripts.lean#L79-L99
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditScripts.lean#L79-L99

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_SingleEditOrigins
import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SingleEditScripts
set_option autoImplicit true
open DeletionCode DeletionCode.SingleEditScripts
open Windows CatalogueWords EditAlignment SingleEditOrigins

theorem DeletionCode.SingleEditScripts.within_one_realized {x y : List Bool} (h : WithinEdits 1 x y) :
    ∃ e : Edit, e.Valid x.length ∧ e.outputLength x.length = y.length ∧
      e.word (listLetters x) = listLetters y := by sorry
