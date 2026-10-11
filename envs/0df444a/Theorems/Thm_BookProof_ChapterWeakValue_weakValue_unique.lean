-- Prove2me | Theorems.Thm_BookProof_ChapterWeakValue_weakValue_unique
-- name    : BookProof.ChapterWeakValue.weakValue_unique
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:11:52.090241+00:00
-- url     : https://prove2.me/theorems/11814c5e-e78d-4aba-a8bf-656f57138401
-- title:
--   `BookProof.ChapterWeakValue.weakValue_unique` (i f : Fin n → ℂ) (A : Matrix (Fin n) (Fin n) ℂ) (h : ip f i ≠ 0) (w : ℂ) (hw : w * ip f i = ip f (A *ᵥ i)) : w = weakValue i f A
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeakValue`.
--
--   `BookProof.ChapterWeakValue.weakValue_unique` (i f : Fin n → ℂ) (A : Matrix (Fin n) (Fin n) ℂ) (h : ip f i ≠ 0) (w : ℂ) (hw : w * ip f i = ip f (A *ᵥ i)) : w = weakValue i f A
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeakValue.weakValue_unique`.

-- Generated from ChapterWeakValue.lean — theorem BookProof.ChapterWeakValue.weakValue_unique
import Mathlib
import Definitions.Def_ChapterWeakValue
open BookProof.ChapterWeakValue


open scoped BigOperators Matrix


variable {n : ℕ}

theorem BookProof.ChapterWeakValue.weakValue_unique (i f : Fin n → ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    (h : ip f i ≠ 0) (w : ℂ) (hw : w * ip f i = ip f (A *ᵥ i)) :
    w = weakValue i f A := by sorry
