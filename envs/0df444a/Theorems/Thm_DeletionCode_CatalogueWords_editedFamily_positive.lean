-- Prove2me | Theorems.Thm_DeletionCode_CatalogueWords_editedFamily_positive
-- name    : DeletionCode.CatalogueWords.editedFamily_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:26:42.996495+00:00
-- url     : https://prove2.me/theorems/f727030f-6924-4280-8f34-d50c2c559f5f
-- title:
--   Catalogue Words: edited Family positive
-- statement:
--   The Catalogue Words construction uses the edited Family positive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueWords.lean#L164-L167
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueWords.lean#L164-L167

import Definitions.Def_DeletionCode_GeneratingModel
import Init.Data.List.Nat.Erase
import Definitions.Def_DeletionCode_CatalogueWords
set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueWords
open Windows HeaderRecovery GeneratingModel

theorem DeletionCode.CatalogueWords.editedFamily_positive {B : Type*} {k : ℕ}
    (bubbles : B → BubbleWord k) (rank : B → ℕ) (b : B) :
    (editedFamily bubbles rank).family.path b true = listLetters (bubbles b).positiveWord := by sorry
