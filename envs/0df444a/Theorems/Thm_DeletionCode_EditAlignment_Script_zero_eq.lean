-- Prove2me | Theorems.Thm_DeletionCode_EditAlignment_Script_zero_eq
-- name    : DeletionCode.EditAlignment.Script.zero_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:29:32.69837+00:00
-- url     : https://prove2.me/theorems/a603faf3-95f4-49f1-9ce6-73ca5c7e40dc
-- title:
--   Script: zero eq
-- statement:
--   A script containing no deletion or insertion leaves its source unchanged.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditScripts.lean#L14-L16
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditScripts.lean#L14-L16

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_SingleEditOrigins
import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SingleEditScripts
set_option autoImplicit true
open DeletionCode DeletionCode.EditAlignment

theorem DeletionCode.EditAlignment.Script.zero_eq {x y : Word} (h : Script x y 0 0) : x = y := by sorry
