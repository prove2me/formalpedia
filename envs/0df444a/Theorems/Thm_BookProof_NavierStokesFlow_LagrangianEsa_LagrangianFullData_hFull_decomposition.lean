-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_LagrangianFullData_hFull_decomposition
-- name    : BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hFull_decomposition
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T11:53:08.813338+00:00
-- url     : https://prove2.me/theorems/b7d03caf-8d60-47a4-867e-db2dc7ea56df
-- title:
--   `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hFull_decomposition` : L.hFull = L.kinetic + L.viscous + L.drift + L.constraintOp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesLagrangianEsa`.
--
--   `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hFull_decomposition` : L.hFull = L.kinetic + L.viscous + L.drift + L.constraintOp
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hFull_decomposition`.

-- Generated from ChapterNavierStokesLagrangianEsa.lean — theorem BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hFull_decomposition
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.ChapterF7
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa




open FullEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)

theorem BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hFull_decomposition :
    L.hFull = L.kinetic + L.viscous + L.drift + L.constraintOp := by sorry
