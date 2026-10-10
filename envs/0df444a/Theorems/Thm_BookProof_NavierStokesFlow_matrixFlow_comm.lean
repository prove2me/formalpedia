-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_matrixFlow_comm
-- name    : BookProof.NavierStokesFlow.matrixFlow_comm
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:38:32.693116+00:00
-- url     : https://prove2.me/theorems/39e90562-9f5f-4e87-8e8f-d29386eed6e6
-- title:
--   `BookProof.NavierStokesFlow.matrixFlow_comm` (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) : matrixFlow A t * A = A * matrixFlow A t
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesCauchy`.
--
--   `BookProof.NavierStokesFlow.matrixFlow_comm` (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) : matrixFlow A t * A = A * matrixFlow A t
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.matrixFlow_comm`.

-- Generated from ChapterNavierStokesCauchy.lean — theorem BookProof.NavierStokesFlow.matrixFlow_comm
import Mathlib
import Definitions.Def_ChapterNavierStokesCauchy
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Matrix.Norms.Operator

variable {n : ℕ}

theorem BookProof.NavierStokesFlow.matrixFlow_comm (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    matrixFlow A t * A = A * matrixFlow A t := by sorry
