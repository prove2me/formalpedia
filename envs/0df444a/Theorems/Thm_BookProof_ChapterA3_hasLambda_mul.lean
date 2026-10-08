-- Prove2me | Theorems.Thm_BookProof_ChapterA3_hasLambda_mul
-- name    : BookProof.ChapterA3.hasLambda_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T12:25:00.808817+00:00
-- url     : https://prove2.me/theorems/a05a42f0-1139-4ed7-8bd8-45c4cc2d4eb9
-- title:
--   `BookProof.ChapterA3.hasLambda_mul` {S₁ S₂ Λ₁ Λ₂ : Matrix (Fin 4) (Fin 4) ℝ} (_h1 : IsUnit S₁.det) (_h2 : IsUnit S₂.det) (hL1 : HasLambda S₁ Λ₁) (hL2 : HasLambda S₂ Λ₂)...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3c`.
--
--   `BookProof.ChapterA3.hasLambda_mul` {S₁ S₂ Λ₁ Λ₂ : Matrix (Fin 4) (Fin 4) ℝ} (_h1 : IsUnit S₁.det) (_h2 : IsUnit S₂.det) (hL1 : HasLambda S₁ Λ₁) (hL2 : HasLambda S₂ Λ₂) : HasLambda (S₁ * S₂) (Λ₁ * Λ₂)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.hasLambda_mul`.

-- Generated from ChapterA3c.lean — theorem BookProof.ChapterA3.hasLambda_mul
import Mathlib
import Definitions.Def_ChapterA3c
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.hasLambda_mul {S₁ S₂ Λ₁ Λ₂ : Matrix (Fin 4) (Fin 4) ℝ}
    (_h1 : IsUnit S₁.det) (_h2 : IsUnit S₂.det)
    (hL1 : HasLambda S₁ Λ₁) (hL2 : HasLambda S₂ Λ₂) :
    HasLambda (S₁ * S₂) (Λ₁ * Λ₂) := by sorry
