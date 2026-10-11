-- Prove2me | Theorems.Thm_BookProof_ChapterWeakValue_projMat_mulVec
-- name    : BookProof.ChapterWeakValue.projMat_mulVec
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:12:44.005732+00:00
-- url     : https://prove2.me/theorems/1a82029b-dd62-4469-a3b8-ccda160da9eb
-- title:
--   `BookProof.ChapterWeakValue.projMat_mulVec` (a : Fin n) (v : Fin n → ℂ) (b : Fin n) : (projMat a *ᵥ v) b = if b = a then v a else 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeakValue`.
--
--   `BookProof.ChapterWeakValue.projMat_mulVec` (a : Fin n) (v : Fin n → ℂ) (b : Fin n) : (projMat a *ᵥ v) b = if b = a then v a else 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeakValue.projMat_mulVec`.

-- Generated from ChapterWeakValue.lean — theorem BookProof.ChapterWeakValue.projMat_mulVec
import Mathlib
import Definitions.Def_ChapterWeakValue
open BookProof.ChapterWeakValue


open scoped BigOperators Matrix


variable {n : ℕ}

theorem BookProof.ChapterWeakValue.projMat_mulVec (a : Fin n) (v : Fin n → ℂ) (b : Fin n) :
    (projMat a *ᵥ v) b = if b = a then v a else 0 := by sorry
