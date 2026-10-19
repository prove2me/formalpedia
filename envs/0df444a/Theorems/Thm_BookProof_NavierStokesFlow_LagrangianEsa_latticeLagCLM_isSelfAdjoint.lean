-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_latticeLagCLM_isSelfAdjoint
-- name    : BookProof.NavierStokesFlow.LagrangianEsa.latticeLagCLM_isSelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T08:32:24.918462+00:00
-- url     : https://prove2.me/theorems/7846d6a4-d176-4e57-8864-9444a921bf33
-- title:
--   `BookProof.NavierStokesFlow.LagrangianEsa.latticeLagCLM_isSelfAdjoint` (v : Fin 3 → LinfZ) (w : LinfZ) (fr : Fin 3 → ℝ) (nu : ℝ) : IsSelfAdjoint (latticeLagCLM v w fr nu)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesLagrangianEsa`.
--
--   `BookProof.NavierStokesFlow.LagrangianEsa.latticeLagCLM_isSelfAdjoint` (v : Fin 3 → LinfZ) (w : LinfZ) (fr : Fin 3 → ℝ) (nu : ℝ) : IsSelfAdjoint (latticeLagCLM v w fr nu)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.LagrangianEsa.latticeLagCLM_isSelfAdjoint`.

-- Generated from ChapterNavierStokesLagrangianEsa.lean — theorem BookProof.NavierStokesFlow.LagrangianEsa.latticeLagCLM_isSelfAdjoint
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterContinuityUnitary
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa




open FullEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)
variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

theorem BookProof.NavierStokesFlow.LagrangianEsa.latticeLagCLM_isSelfAdjoint (v : Fin 3 → LinfZ) (w : LinfZ) (fr : Fin 3 → ℝ) (nu : ℝ) :
    IsSelfAdjoint (latticeLagCLM v w fr nu) := by sorry
