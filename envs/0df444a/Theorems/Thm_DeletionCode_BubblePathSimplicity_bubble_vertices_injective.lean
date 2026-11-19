-- Prove2me | Theorems.Thm_DeletionCode_BubblePathSimplicity_bubble_vertices_injective
-- name    : DeletionCode.BubblePathSimplicity.bubble_vertices_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:24:30.974215+00:00
-- url     : https://prove2.me/theorems/4d7edbcf-2f42-4ff8-b6ae-034c3bb8b40a
-- title:
--   Bubble Path Simplicity: bubble vertices injective
-- statement:
--   The grammar lengths give exactly the two vertex-index types in the paper.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubblePathSimplicity.lean#L55-L101
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubblePathSimplicity.lean#L55-L101

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_EditRigidity
import Definitions.Def_DeletionCode_BubblePathSimplicity
set_option autoImplicit true
open DeletionCode DeletionCode.BubblePathSimplicity
open Windows HeaderRecovery CatalogueWords SingleEditOrigins

theorem DeletionCode.BubblePathSimplicity.bubble_vertices_injective {k : ℕ} (bubble : BubbleWord k)
    (hlong : KUnique (listLetters bubble.longWord) bubble.longWord.length (windowLength k - 1))
    (hshort : KUnique (listLetters bubble.shortWord) bubble.shortWord.length (windowLength k - 1)) :
    Function.Injective (fun i : Fin (windowLength k - bubble.rho + 2) =>
      SpectrumPath.vertexAt (listLetters bubble.longWord) (windowLength k) i.val) ∧
    Function.Injective (fun i : Fin (windowLength k - bubble.rho + 1) =>
      SpectrumPath.vertexAt (listLetters bubble.shortWord) (windowLength k) i.val) := by sorry
