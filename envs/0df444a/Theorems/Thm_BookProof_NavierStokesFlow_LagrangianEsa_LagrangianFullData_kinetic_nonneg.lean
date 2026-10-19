-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_LagrangianFullData_kinetic_nonneg
-- name    : BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.kinetic_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T08:15:28.821674+00:00
-- url     : https://prove2.me/theorems/3e75d590-20f8-49ce-98c9-a74b3f2f5fd2
-- title:
--   `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.kinetic_nonneg` (v : L.D) : 0 ≤ (inner ℂ (v : F) (L.kinetic v : F) : ℂ).re
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesLagrangianEsa`.
--
--   `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.kinetic_nonneg` (v : L.D) : 0 ≤ (inner ℂ (v : F) (L.kinetic v : F) : ℂ).re
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.kinetic_nonneg`.

-- Generated from ChapterNavierStokesLagrangianEsa.lean — theorem BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.kinetic_nonneg
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.ChapterF7
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa




open FullEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)

theorem BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.kinetic_nonneg (v : L.D) : 0 ≤ (inner ℂ (v : F) (L.kinetic v : F) : ℂ).re := by sorry
