-- Prove2me | Theorems.Thm_BookProof_GhostField_psiDag_sq
-- name    : BookProof.GhostField.psiDag_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:34:20.691289+00:00
-- url     : https://prove2.me/theorems/b5082654-67a2-42ec-8e32-4f80d2fa30d5
-- title:
--   The ghost creation operator is nilpotent: `ψ†² = 0` (Pauli exclusion — a fermionic mode cannot be occupied twice)
-- statement:
--   The ghost creation operator is nilpotent: `ψ†² = 0` (Pauli exclusion — a
--   fermionic mode cannot be occupied twice).
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.GhostField.psiDag_sq` (module `BookProof.GhostField`), line-linked source: `ChapterGhostField.lean` lines 71–74.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGhostField.lean#L71-L74

-- Generated from ChapterGhostField.lean — theorem BookProof.GhostField.psiDag_sq
import Mathlib
import Definitions.Def_ChapterGhostField
open BookProof.GhostField










open Matrix

theorem BookProof.GhostField.psiDag_sq : psiDag * psiDag = 0 := by sorry
