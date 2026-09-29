-- Prove2me | Theorems.Thm_BookProof_GhostField_numberOp_idempotent
-- name    : BookProof.GhostField.numberOp_idempotent
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:32:27.910581+00:00
-- url     : https://prove2.me/theorems/b2934401-d195-40d8-8b44-ff1072633995
-- title:
--   The number operator is idempotent: `N² = N`
-- statement:
--   The number operator is idempotent: `N² = N`. Together with self-adjointness
--   this says `N` is an **orthogonal projection**, so the ghost occupation number is
--   `0` or `1`.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.GhostField.numberOp_idempotent` (module `BookProof.GhostField`), line-linked source: `ChapterGhostField.lean` lines 94–99.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGhostField.lean#L94-L99

-- Generated from ChapterGhostField.lean — theorem BookProof.GhostField.numberOp_idempotent
import Mathlib
import Definitions.Def_ChapterGhostField
open BookProof.GhostField










open Matrix

theorem BookProof.GhostField.numberOp_idempotent : numberOp * numberOp = numberOp := by sorry
