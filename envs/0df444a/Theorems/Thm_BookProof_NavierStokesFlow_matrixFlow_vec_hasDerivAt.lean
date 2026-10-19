-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_matrixFlow_vec_hasDerivAt
-- name    : BookProof.NavierStokesFlow.matrixFlow_vec_hasDerivAt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:17:39.572204+00:00
-- url     : https://prove2.me/theorems/d7c09f9a-7959-4402-b184-e1b5b32d5449
-- title:
--   `BookProof.NavierStokesFlow.matrixFlow_vec_hasDerivAt` (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) (t : ℝ) : HasDerivAt (fun s : ℝ => matrixFlow A s *ᵥ x) (A *ᵥ (matrixFlow A t
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesCauchy`.
--
--   `BookProof.NavierStokesFlow.matrixFlow_vec_hasDerivAt` (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) (t : ℝ) : HasDerivAt (fun s : ℝ => matrixFlow A s *ᵥ x) (A *ᵥ (matrixFlow A t *ᵥ x)) t
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.matrixFlow_vec_hasDerivAt`.

-- Generated from ChapterNavierStokesCauchy.lean — theorem BookProof.NavierStokesFlow.matrixFlow_vec_hasDerivAt
import Mathlib
import Definitions.Def_ChapterNavierStokesCauchy
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Matrix.Norms.Operator

variable {n : ℕ}

theorem BookProof.NavierStokesFlow.matrixFlow_vec_hasDerivAt (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => matrixFlow A s *ᵥ x) (A *ᵥ (matrixFlow A t *ᵥ x)) t := by sorry
