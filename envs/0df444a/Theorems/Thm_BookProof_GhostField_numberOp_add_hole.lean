-- Prove2me | Theorems.Thm_BookProof_GhostField_numberOp_add_hole
-- name    : BookProof.GhostField.numberOp_add_hole
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:31:21.038075+00:00
-- url     : https://prove2.me/theorems/692a5a52-a76f-4f24-802a-e535d28b98ac
-- title:
--   Completeness of the two occupation projectors: `ψ†ψ + ψψ† = 1` (occupied plus empty exhaust the ghost factor)
-- statement:
--   Completeness of the two occupation projectors: `ψ†ψ + ψψ† = 1`
--   (occupied plus empty exhaust the ghost factor).
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.GhostField.numberOp_add_hole` (module `BookProof.GhostField`), line-linked source: `ChapterGhostField.lean` lines 106–110.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGhostField.lean#L106-L110

-- Generated from ChapterGhostField.lean — theorem BookProof.GhostField.numberOp_add_hole
import Mathlib
import Definitions.Def_ChapterGhostField
open BookProof.GhostField










open Matrix

theorem BookProof.GhostField.numberOp_add_hole : numberOp + psi * psiDag = 1 := by sorry
