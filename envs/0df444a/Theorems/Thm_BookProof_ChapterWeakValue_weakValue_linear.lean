-- Prove2me | Theorems.Thm_BookProof_ChapterWeakValue_weakValue_linear
-- name    : BookProof.ChapterWeakValue.weakValue_linear
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:12:17.870317+00:00
-- url     : https://prove2.me/theorems/38668dd1-e031-4e57-b9b5-a1d4383c5a5b
-- title:
--   `BookProof.ChapterWeakValue.weakValue_linear` (c d : ℂ) (i f : Fin n → ℂ) (A B : Matrix (Fin n) (Fin n) ℂ) : weakValue i f (c • A + d • B) = c * weakValue i f A + d * weakValue i f
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeakValue`.
--
--   `BookProof.ChapterWeakValue.weakValue_linear` (c d : ℂ) (i f : Fin n → ℂ) (A B : Matrix (Fin n) (Fin n) ℂ) : weakValue i f (c • A + d • B) = c * weakValue i f A + d * weakValue i f B
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeakValue.weakValue_linear`.

-- Generated from ChapterWeakValue.lean — theorem BookProof.ChapterWeakValue.weakValue_linear
import Mathlib
import Definitions.Def_ChapterWeakValue
open BookProof.ChapterWeakValue


open scoped BigOperators Matrix


variable {n : ℕ}

theorem BookProof.ChapterWeakValue.weakValue_linear (c d : ℂ) (i f : Fin n → ℂ)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    weakValue i f (c • A + d • B) =
      c * weakValue i f A + d * weakValue i f B := by sorry
