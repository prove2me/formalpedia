-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_jacobiLagData_hFull
-- name    : BookProof.NavierStokesFlow.LagrangianEsa.jacobiLagData_hFull
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T08:15:37.810054+00:00
-- url     : https://prove2.me/theorems/63191712-f4d7-4767-a402-1cbc6e428f9f
-- title:
--   `BookProof.NavierStokesFlow.LagrangianEsa.jacobiLagData_hFull` : jacobiLagData.hFull = jacobiOp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesLagrangianEsa`.
--
--   `BookProof.NavierStokesFlow.LagrangianEsa.jacobiLagData_hFull` : jacobiLagData.hFull = jacobiOp
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.LagrangianEsa.jacobiLagData_hFull`.

-- Generated from ChapterNavierStokesLagrangianEsa.lean — theorem BookProof.NavierStokesFlow.LagrangianEsa.jacobiLagData_hFull
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.BRSTNilpotent
open BookProof.ChapterF7
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

theorem BookProof.NavierStokesFlow.LagrangianEsa.jacobiLagData_hFull : jacobiLagData.hFull = jacobiOp := by sorry
