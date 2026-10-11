-- Prove2me | Theorems.Thm_BookProof_ChapterWeakValue_ip_conj_mulVec
-- name    : BookProof.ChapterWeakValue.ip_conj_mulVec
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:11:26.042978+00:00
-- url     : https://prove2.me/theorems/04ce35e7-778f-4750-9102-664f53506c8f
-- title:
--   `BookProof.ChapterWeakValue.ip_conj_mulVec` (A : Matrix (Fin n) (Fin n) ℂ) (f v : Fin n → ℂ) : starRingEnd ℂ (ip f (A *ᵥ v)) = ip v (Aᴴ *ᵥ f)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeakValue`.
--
--   `BookProof.ChapterWeakValue.ip_conj_mulVec` (A : Matrix (Fin n) (Fin n) ℂ) (f v : Fin n → ℂ) : starRingEnd ℂ (ip f (A *ᵥ v)) = ip v (Aᴴ *ᵥ f)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeakValue.ip_conj_mulVec`.

-- Generated from ChapterWeakValue.lean — theorem BookProof.ChapterWeakValue.ip_conj_mulVec
import Mathlib
import Definitions.Def_ChapterWeakValue
open BookProof.ChapterWeakValue


open scoped BigOperators Matrix


variable {n : ℕ}

theorem BookProof.ChapterWeakValue.ip_conj_mulVec (A : Matrix (Fin n) (Fin n) ℂ) (f v : Fin n → ℂ) :
    starRingEnd ℂ (ip f (A *ᵥ v)) = ip v (Aᴴ *ᵥ f) := by sorry
