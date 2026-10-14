-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_matrixFlow_neg_hasDerivAt
-- name    : BookProof.NavierStokesFlow.matrixFlow_neg_hasDerivAt
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T19:16:49.88919+00:00
-- url     : https://prove2.me/theorems/9267f91e-4fa2-452b-bf80-77617289831e
-- title:
--   `BookProof.NavierStokesFlow.matrixFlow_neg_hasDerivAt` (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) : HasDerivAt (fun s : ℝ => matrixFlow A (-s)) (-(matrixFlow A (-t) * A)) t
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesCauchy`.
--
--   `BookProof.NavierStokesFlow.matrixFlow_neg_hasDerivAt` (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) : HasDerivAt (fun s : ℝ => matrixFlow A (-s)) (-(matrixFlow A (-t) * A)) t
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.matrixFlow_neg_hasDerivAt`.

-- Generated from ChapterNavierStokesCauchy.lean — theorem BookProof.NavierStokesFlow.matrixFlow_neg_hasDerivAt
import Mathlib
import Definitions.Def_ChapterNavierStokesCauchy
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Matrix.Norms.Operator

variable {n : ℕ}

theorem BookProof.NavierStokesFlow.matrixFlow_neg_hasDerivAt (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => matrixFlow A (-s)) (-(matrixFlow A (-t) * A)) t := by sorry
