-- Prove2me | Theorems.Thm_BookProof_ChapterWeakValue_weakValue_smul
-- name    : BookProof.ChapterWeakValue.weakValue_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:12:05.927681+00:00
-- url     : https://prove2.me/theorems/4cbd493d-ba12-4f4e-a20d-5c5700b537a3
-- title:
--   `BookProof.ChapterWeakValue.weakValue_smul` (c : ℂ) (i f : Fin n → ℂ) (A : Matrix (Fin n) (Fin n) ℂ) : weakValue i f (c • A) = c * weakValue i f A
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeakValue`.
--
--   `BookProof.ChapterWeakValue.weakValue_smul` (c : ℂ) (i f : Fin n → ℂ) (A : Matrix (Fin n) (Fin n) ℂ) : weakValue i f (c • A) = c * weakValue i f A
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeakValue.weakValue_smul`.

-- Generated from ChapterWeakValue.lean — theorem BookProof.ChapterWeakValue.weakValue_smul
import Mathlib
import Definitions.Def_ChapterWeakValue
open BookProof.ChapterWeakValue


open scoped BigOperators Matrix


variable {n : ℕ}

theorem BookProof.ChapterWeakValue.weakValue_smul (c : ℂ) (i f : Fin n → ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    weakValue i f (c • A) = c * weakValue i f A := by sorry
