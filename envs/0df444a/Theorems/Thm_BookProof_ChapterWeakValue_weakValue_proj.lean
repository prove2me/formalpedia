-- Prove2me | Theorems.Thm_BookProof_ChapterWeakValue_weakValue_proj
-- name    : BookProof.ChapterWeakValue.weakValue_proj
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:12:37.877996+00:00
-- url     : https://prove2.me/theorems/25479a84-187c-4988-8e0c-e7ccfaf5dd94
-- title:
--   `BookProof.ChapterWeakValue.weakValue_proj` (i f : Fin n → ℂ) (a : Fin n) : weakValue i f (projMat a) = starRingEnd ℂ (f a) * i a / ip f i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeakValue`.
--
--   `BookProof.ChapterWeakValue.weakValue_proj` (i f : Fin n → ℂ) (a : Fin n) : weakValue i f (projMat a) = starRingEnd ℂ (f a) * i a / ip f i
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeakValue.weakValue_proj`.

-- Generated from ChapterWeakValue.lean — theorem BookProof.ChapterWeakValue.weakValue_proj
import Mathlib
import Definitions.Def_ChapterWeakValue
open BookProof.ChapterWeakValue


open scoped BigOperators Matrix


variable {n : ℕ}

theorem BookProof.ChapterWeakValue.weakValue_proj (i f : Fin n → ℂ) (a : Fin n) :
    weakValue i f (projMat a) = starRingEnd ℂ (f a) * i a / ip f i := by sorry
