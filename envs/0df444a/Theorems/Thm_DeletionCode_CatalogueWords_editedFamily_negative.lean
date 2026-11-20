-- Prove2me | Theorems.Thm_DeletionCode_CatalogueWords_editedFamily_negative
-- name    : DeletionCode.CatalogueWords.editedFamily_negative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:26:37.840027+00:00
-- url     : https://prove2.me/theorems/f85caf2e-9651-4876-9170-1f7f978e4e51
-- title:
--   Catalogue Words: edited Family negative
-- statement:
--   The Catalogue Words construction uses the edited Family negative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueWords.lean#L159-L162
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueWords.lean#L159-L162

import Definitions.Def_DeletionCode_GeneratingModel
import Init.Data.List.Nat.Erase
import Definitions.Def_DeletionCode_CatalogueWords
set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueWords
open Windows HeaderRecovery GeneratingModel

theorem DeletionCode.CatalogueWords.editedFamily_negative {B : Type*} {k : ℕ}
    (bubbles : B → BubbleWord k) (rank : B → ℕ) (b : B) :
    (editedFamily bubbles rank).family.path b false = listLetters (bubbles b).negativeWord := by sorry
