-- Prove2me | Theorems.Thm_DeletionCode_BubblePathSimplicity_local_vertex_injective
-- name    : DeletionCode.BubblePathSimplicity.local_vertex_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:16:44.455456+00:00
-- url     : https://prove2.me/theorems/a5031844-d0b7-4944-8624-f43ad4d4a476
-- title:
--   Bubble Path Simplicity: local vertex injective
-- statement:
--   All vertices of such a local path, including its terminal vertex, are distinct.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubblePathSimplicity.lean#L42-L52
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubblePathSimplicity.lean#L42-L52

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_EditRigidity
import Definitions.Def_DeletionCode_BubblePathSimplicity
set_option autoImplicit true
open DeletionCode DeletionCode.BubblePathSimplicity
open Windows HeaderRecovery CatalogueWords SingleEditOrigins

theorem DeletionCode.BubblePathSimplicity.local_vertex_injective {n k : ℕ} (hk : 1 ≤ k) (x : Letters)
    (hx : KUnique x n k) (e : Edit) (he : e.Valid n)
    (word : List Bool) (s : ℕ)
    (hbound : s + word.length ≤ e.outputLength n)
    (hocc : Agree (listLetters word) 0 (e.word x) s word.length)
    (hlength : windowLength k ≤ word.length) :
    Function.Injective (fun i : Fin (word.length - windowLength k + 2) =>
      SpectrumPath.vertexAt (listLetters word) (windowLength k) i.val) := by sorry
