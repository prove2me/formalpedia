-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_matrixFlow_hasDerivAt
-- name    : BookProof.NavierStokesFlow.matrixFlow_hasDerivAt
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:39:06.975614+00:00
-- url     : https://prove2.me/theorems/4dafced1-4a88-408c-9d41-d17e54be2396
-- title:
--   `BookProof.NavierStokesFlow.matrixFlow_hasDerivAt` (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) : HasDerivAt (matrixFlow A) (matrixFlow A t * A) t
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesCauchy`.
--
--   `BookProof.NavierStokesFlow.matrixFlow_hasDerivAt` (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) : HasDerivAt (matrixFlow A) (matrixFlow A t * A) t
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.matrixFlow_hasDerivAt`.

-- Generated from ChapterNavierStokesCauchy.lean — theorem BookProof.NavierStokesFlow.matrixFlow_hasDerivAt
import Mathlib
import Definitions.Def_ChapterNavierStokesCauchy
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Matrix.Norms.Operator

variable {n : ℕ}

theorem BookProof.NavierStokesFlow.matrixFlow_hasDerivAt (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    HasDerivAt (matrixFlow A) (matrixFlow A t * A) t := by sorry
