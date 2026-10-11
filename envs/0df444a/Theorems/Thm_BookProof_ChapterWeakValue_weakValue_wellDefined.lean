-- Prove2me | Theorems.Thm_BookProof_ChapterWeakValue_weakValue_wellDefined
-- name    : BookProof.ChapterWeakValue.weakValue_wellDefined
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:11:39.636475+00:00
-- url     : https://prove2.me/theorems/831a0daa-1ad1-4e6b-b994-ca1975072ce5
-- title:
--   `BookProof.ChapterWeakValue.weakValue_wellDefined` (i f : Fin n → ℂ) (A : Matrix (Fin n) (Fin n) ℂ) (h : ip f i ≠ 0) : weakValue i f A * ip f i = ip f (A *ᵥ i)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeakValue`.
--
--   `BookProof.ChapterWeakValue.weakValue_wellDefined` (i f : Fin n → ℂ) (A : Matrix (Fin n) (Fin n) ℂ) (h : ip f i ≠ 0) : weakValue i f A * ip f i = ip f (A *ᵥ i)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeakValue.weakValue_wellDefined`.

-- Generated from ChapterWeakValue.lean — theorem BookProof.ChapterWeakValue.weakValue_wellDefined
import Mathlib
import Definitions.Def_ChapterWeakValue
open BookProof.ChapterWeakValue


open scoped BigOperators Matrix


variable {n : ℕ}

theorem BookProof.ChapterWeakValue.weakValue_wellDefined (i f : Fin n → ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    (h : ip f i ≠ 0) : weakValue i f A * ip f i = ip f (A *ᵥ i) := by sorry
