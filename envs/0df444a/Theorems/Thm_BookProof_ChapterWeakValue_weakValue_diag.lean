-- Prove2me | Theorems.Thm_BookProof_ChapterWeakValue_weakValue_diag
-- name    : BookProof.ChapterWeakValue.weakValue_diag
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:12:33.647998+00:00
-- url     : https://prove2.me/theorems/df8ce168-f95e-4f9d-8fcb-7e77a4626647
-- title:
--   `BookProof.ChapterWeakValue.weakValue_diag` (i : Fin n → ℂ) (A : Matrix (Fin n) (Fin n) ℂ) (hi : ip i i = 1) : weakValue i i A = ip i (A *ᵥ i)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeakValue`.
--
--   `BookProof.ChapterWeakValue.weakValue_diag` (i : Fin n → ℂ) (A : Matrix (Fin n) (Fin n) ℂ) (hi : ip i i = 1) : weakValue i i A = ip i (A *ᵥ i)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeakValue.weakValue_diag`.

-- Generated from ChapterWeakValue.lean — theorem BookProof.ChapterWeakValue.weakValue_diag
import Mathlib
import Definitions.Def_ChapterWeakValue
open BookProof.ChapterWeakValue


open scoped BigOperators Matrix


variable {n : ℕ}

theorem BookProof.ChapterWeakValue.weakValue_diag (i : Fin n → ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    (hi : ip i i = 1) : weakValue i i A = ip i (A *ᵥ i) := by sorry
