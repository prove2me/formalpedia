-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_diagLag_hasZeroDeficiencyOn
-- name    : BookProof.NavierStokesFlow.LagrangianEsa.diagLag_hasZeroDeficiencyOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T19:20:45.728977+00:00
-- url     : https://prove2.me/theorems/8445e745-05a8-43b1-a8d5-562828f2a54d
-- title:
--   `BookProof.NavierStokesFlow.LagrangianEsa.diagLag_hasZeroDeficiencyOn` : diagLagUnbounded.hFull = diagOp (fun n => (1 / 2) * (n : ℝ) ^ 2)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesLagrangianEsa`.
--
--   `BookProof.NavierStokesFlow.LagrangianEsa.diagLag_hasZeroDeficiencyOn` : diagLagUnbounded.hFull = diagOp (fun n => (1 / 2) * (n : ℝ) ^ 2)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.LagrangianEsa.diagLag_hasZeroDeficiencyOn`.

-- Generated from ChapterNavierStokesLagrangianEsa.lean — theorem BookProof.NavierStokesFlow.LagrangianEsa.diagLag_hasZeroDeficiencyOn
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.NavierStokesFlow.DiagonalEsa
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow.LpNat
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa




open FullEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)
variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

theorem BookProof.NavierStokesFlow.LagrangianEsa.diagLag_hasZeroDeficiencyOn :
    diagLagUnbounded.hFull = diagOp (fun n => (1 / 2) * (n : ℝ) ^ 2) := by sorry
