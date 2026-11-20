-- Prove2me | Theorems.Thm_DeletionCode_BubblePathSimplicity_substring_unique
-- name    : DeletionCode.BubblePathSimplicity.substring_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:39:30.563197+00:00
-- url     : https://prove2.me/theorems/e5ccdade-f8c0-4d4a-a175-4f4a8457c870
-- title:
--   Bubble Path Simplicity: substring unique
-- statement:
--   Uniqueness restricts to any actual in-bounds substring.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubblePathSimplicity.lean#L16-L29
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubblePathSimplicity.lean#L16-L29

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_EditRigidity
import Definitions.Def_DeletionCode_BubblePathSimplicity
set_option autoImplicit true
open DeletionCode DeletionCode.BubblePathSimplicity
open Windows HeaderRecovery CatalogueWords SingleEditOrigins

theorem DeletionCode.BubblePathSimplicity.substring_unique (full word : Letters) (n len r s : ℕ)
    (hfull : KUnique full n r) (hbound : s + len ≤ n)
    (hocc : Agree word 0 full s len) : KUnique word len r := by sorry
