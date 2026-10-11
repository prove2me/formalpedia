-- Prove2me | Theorems.Thm_BookProof_ChapterWeakValue_weakValue_diag_isReal
-- name    : BookProof.ChapterWeakValue.weakValue_diag_isReal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:12:45.332448+00:00
-- url     : https://prove2.me/theorems/76d0bc2a-46c6-4420-82fd-ddfc95ef9673
-- title:
--   `BookProof.ChapterWeakValue.weakValue_diag_isReal` (i : Fin n → ℂ) (A : Matrix (Fin n) (Fin n) ℂ) (hA : Aᴴ = A) (hi : ip i i = 1) : starRingEnd ℂ (weakValue i i A) = weakValue i i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeakValue`.
--
--   `BookProof.ChapterWeakValue.weakValue_diag_isReal` (i : Fin n → ℂ) (A : Matrix (Fin n) (Fin n) ℂ) (hA : Aᴴ = A) (hi : ip i i = 1) : starRingEnd ℂ (weakValue i i A) = weakValue i i A
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeakValue.weakValue_diag_isReal`.

-- Generated from ChapterWeakValue.lean — theorem BookProof.ChapterWeakValue.weakValue_diag_isReal
import Mathlib
import Definitions.Def_ChapterWeakValue
open BookProof.ChapterWeakValue


open scoped BigOperators Matrix


variable {n : ℕ}

theorem BookProof.ChapterWeakValue.weakValue_diag_isReal (i : Fin n → ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : Aᴴ = A) (hi : ip i i = 1) :
    starRingEnd ℂ (weakValue i i A) = weakValue i i A := by sorry
