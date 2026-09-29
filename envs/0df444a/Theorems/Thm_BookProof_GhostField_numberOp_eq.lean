-- Prove2me | Theorems.Thm_BookProof_GhostField_numberOp_eq
-- name    : BookProof.GhostField.numberOp_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:31:58.691363+00:00
-- url     : https://prove2.me/theorems/87a28515-49f3-4377-b85c-11b3c7895404
-- title:
--   The number operator explicitly
-- statement:
--   The number operator explicitly. With the book's convention (`ψ†` sends the
--   component at index `1` to index `0`), `N = ψ†ψ = |0⟩⟨0|` is the projector onto
--   the index-`0` occupation state.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.GhostField.numberOp_eq` (module `BookProof.GhostField`), line-linked source: `ChapterGhostField.lean` lines 87–92.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGhostField.lean#L87-L92

-- Generated from ChapterGhostField.lean — theorem BookProof.GhostField.numberOp_eq
import Mathlib
import Definitions.Def_ChapterGhostField
open BookProof.GhostField










open Matrix

theorem BookProof.GhostField.numberOp_eq : numberOp = !![1, 0; 0, 0] := by sorry
