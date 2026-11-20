-- Prove2me | Theorems.Thm_DeletionCode_BubblePathSimplicity_deletion_vertices_injective
-- name    : DeletionCode.BubblePathSimplicity.deletion_vertices_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:38:54.254061+00:00
-- url     : https://prove2.me/theorems/a77634c1-274d-4109-b8c4-5adb74c8640f
-- title:
--   Bubble Path Simplicity: deletion vertices injective
-- statement:
--   The actual longer source substring and shorter deletion substring both
--   spell simple paths, with exactly the manuscript's long and short vertex ranges.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubblePathSimplicity.lean#L105-L117
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubblePathSimplicity.lean#L105-L117

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_EditRigidity
import Definitions.Def_DeletionCode_BubblePathSimplicity
set_option autoImplicit true
open DeletionCode DeletionCode.BubblePathSimplicity
open Windows HeaderRecovery CatalogueWords SingleEditOrigins

theorem DeletionCode.BubblePathSimplicity.deletion_vertices_injective {n k : ℕ} (hk : 1 ≤ k) (bubble : BubbleWord k)
    (x : Letters) (hx : KUnique x n k) (pos : ℕ) (hpos : pos < n) (s : ℕ)
    (hlength : s + bubble.longWord.length ≤ n)
    (hslength : s + bubble.shortWord.length ≤ n - 1)
    (hlong : Agree (listLetters bubble.longWord) 0 x s bubble.longWord.length)
    (hshort : Agree (listLetters bubble.shortWord) 0 (deleteAt x pos) s bubble.shortWord.length) :
    Function.Injective (fun i : Fin (windowLength k - bubble.rho + 2) =>
      SpectrumPath.vertexAt (listLetters bubble.longWord) (windowLength k) i.val) ∧
    Function.Injective (fun i : Fin (windowLength k - bubble.rho + 1) =>
      SpectrumPath.vertexAt (listLetters bubble.shortWord) (windowLength k) i.val) := by sorry
