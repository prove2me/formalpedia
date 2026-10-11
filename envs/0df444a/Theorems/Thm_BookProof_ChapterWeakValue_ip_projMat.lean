-- Prove2me | Theorems.Thm_BookProof_ChapterWeakValue_ip_projMat
-- name    : BookProof.ChapterWeakValue.ip_projMat
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:12:38.250262+00:00
-- url     : https://prove2.me/theorems/808c21c4-8bd9-424b-abd1-29bf52c175da
-- title:
--   `BookProof.ChapterWeakValue.ip_projMat` (a : Fin n) (f v : Fin n → ℂ) : ip f (projMat a *ᵥ v) = starRingEnd ℂ (f a) * v a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeakValue`.
--
--   `BookProof.ChapterWeakValue.ip_projMat` (a : Fin n) (f v : Fin n → ℂ) : ip f (projMat a *ᵥ v) = starRingEnd ℂ (f a) * v a
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeakValue.ip_projMat`.

-- Generated from ChapterWeakValue.lean — theorem BookProof.ChapterWeakValue.ip_projMat
import Mathlib
import Definitions.Def_ChapterWeakValue
open BookProof.ChapterWeakValue


open scoped BigOperators Matrix


variable {n : ℕ}

theorem BookProof.ChapterWeakValue.ip_projMat (a : Fin n) (f v : Fin n → ℂ) :
    ip f (projMat a *ᵥ v) = starRingEnd ℂ (f a) * v a := by sorry
