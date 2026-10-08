-- Prove2me | Theorems.Thm_BookProof_ChapterA3_lorentz_of_conjR
-- name    : BookProof.ChapterA3.lorentz_of_conjR
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T12:20:47.183121+00:00
-- url     : https://prove2.me/theorems/cb7359d4-1b68-45d0-a372-5a7a4a3a90d1
-- title:
--   `BookProof.ChapterA3.lorentz_of_conjR` (S : Matrix (Fin 4) (Fin 4) ℝ) (hS : IsUnit S.det) (Λ : Matrix (Fin 4) (Fin 4) ℝ) (hΛ : HasLambda S Λ) : Λ * minkowskiMat * Λᵀ = minkowskiMat
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3c`.
--
--   `BookProof.ChapterA3.lorentz_of_conjR` (S : Matrix (Fin 4) (Fin 4) ℝ) (hS : IsUnit S.det) (Λ : Matrix (Fin 4) (Fin 4) ℝ) (hΛ : HasLambda S Λ) : Λ * minkowskiMat * Λᵀ = minkowskiMat
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.lorentz_of_conjR`.

-- Generated from ChapterA3c.lean — theorem BookProof.ChapterA3.lorentz_of_conjR
import Mathlib
import Definitions.Def_ChapterA3c
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3b
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.lorentz_of_conjR (S : Matrix (Fin 4) (Fin 4) ℝ) (hS : IsUnit S.det)
    (Λ : Matrix (Fin 4) (Fin 4) ℝ) (hΛ : HasLambda S Λ) :
    Λ * minkowskiMat * Λᵀ = minkowskiMat := by sorry
