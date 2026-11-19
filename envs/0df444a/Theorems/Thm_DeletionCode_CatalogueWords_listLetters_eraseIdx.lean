-- Prove2me | Theorems.Thm_DeletionCode_CatalogueWords_listLetters_eraseIdx
-- name    : DeletionCode.CatalogueWords.listLetters_eraseIdx
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:19:16.634011+00:00
-- url     : https://prove2.me/theorems/fc7b714b-640d-4f19-9195-8dc46f724d79
-- title:
--   Catalogue Words: list Letters erase Idx
-- statement:
--   Deleting a list entry agrees everywhere with deletion of its padded letters.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueWords.lean#L19-L23
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueWords.lean#L19-L23

import Definitions.Def_DeletionCode_GeneratingModel
import Init.Data.List.Nat.Erase
import Definitions.Def_DeletionCode_CatalogueWords
set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueWords
open Windows HeaderRecovery GeneratingModel

theorem DeletionCode.CatalogueWords.listLetters_eraseIdx (word : List Bool) (ell : ℕ) :
    listLetters (word.eraseIdx ell) = deleteAt (listLetters word) ell := by sorry
