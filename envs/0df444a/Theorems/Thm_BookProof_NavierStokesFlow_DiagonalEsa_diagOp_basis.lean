-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DiagonalEsa_diagOp_basis
-- name    : BookProof.NavierStokesFlow.DiagonalEsa.diagOp_basis
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:09:26.139236+00:00
-- url     : https://prove2.me/theorems/d99ecc9d-46fa-496e-8ab0-d2b3c7ccbd83
-- title:
--   `BookProof.NavierStokesFlow.DiagonalEsa.diagOp_basis` (c : ℕ → ℝ) (n : ℕ) : diagOp c (basis n) = ((c n : ℂ)) • basis n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesDeficiency`.
--
--   `BookProof.NavierStokesFlow.DiagonalEsa.diagOp_basis` (c : ℕ → ℝ) (n : ℕ) : diagOp c (basis n) = ((c n : ℂ)) • basis n
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.DiagonalEsa.diagOp_basis`.

-- Generated from ChapterNavierStokesDeficiency.lean — theorem BookProof.NavierStokesFlow.DiagonalEsa.diagOp_basis
import Mathlib
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.DiagonalEsa


open scoped ENNReal

theorem BookProof.NavierStokesFlow.DiagonalEsa.diagOp_basis (c : ℕ → ℝ) (n : ℕ) : diagOp c (basis n) = ((c n : ℂ)) • basis n := by sorry
