-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_matrixFlow_mul_neg
-- name    : BookProof.NavierStokesFlow.matrixFlow_mul_neg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:16:19.307845+00:00
-- url     : https://prove2.me/theorems/aa14eb1a-a3f4-405e-94a8-b6663d74d71a
-- title:
--   `BookProof.NavierStokesFlow.matrixFlow_mul_neg` (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) : matrixFlow A t * matrixFlow A (-t) = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesCauchy`.
--
--   `BookProof.NavierStokesFlow.matrixFlow_mul_neg` (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) : matrixFlow A t * matrixFlow A (-t) = 1
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.matrixFlow_mul_neg`.

-- Generated from ChapterNavierStokesCauchy.lean — theorem BookProof.NavierStokesFlow.matrixFlow_mul_neg
import Mathlib
import Definitions.Def_ChapterNavierStokesCauchy
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Matrix.Norms.Operator

variable {n : ℕ}

theorem BookProof.NavierStokesFlow.matrixFlow_mul_neg (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    matrixFlow A t * matrixFlow A (-t) = 1 := by sorry
