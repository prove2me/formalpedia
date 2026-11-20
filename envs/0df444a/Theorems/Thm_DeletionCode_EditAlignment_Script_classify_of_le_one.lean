-- Prove2me | Theorems.Thm_DeletionCode_EditAlignment_Script_classify_of_le_one
-- name    : DeletionCode.EditAlignment.Script.classify_of_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:29:34.266216+00:00
-- url     : https://prove2.me/theorems/ce163d90-e6b6-4aa5-9202-2a638cb2c593
-- title:
--   Script: classify of le one
-- statement:
--   A script of total cost at most one is unchanged, one deletion, or one insertion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditScripts.lean#L19-L39
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditScripts.lean#L19-L39

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_SingleEditOrigins
import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SingleEditScripts
set_option autoImplicit true
open DeletionCode DeletionCode.EditAlignment

theorem DeletionCode.EditAlignment.Script.classify_of_le_one {x y : Word} {d i : ℕ}
    (h : Script x y d i) (hcost : d + i ≤ 1) :
    x = y ∨
      (∃ (pre suffix : Word) (bit : Bool),
        x = pre ++ bit :: suffix ∧ y = pre ++ suffix) ∨
      (∃ (pre suffix : Word) (bit : Bool),
        x = pre ++ suffix ∧ y = pre ++ bit :: suffix) := by sorry
