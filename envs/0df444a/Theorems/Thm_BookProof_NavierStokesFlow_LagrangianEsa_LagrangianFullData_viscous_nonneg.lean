-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_LagrangianFullData_viscous_nonneg
-- name    : BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.viscous_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T08:15:17.621977+00:00
-- url     : https://prove2.me/theorems/5949a811-850d-4930-be84-30b2ceacd616
-- title:
--   `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.viscous_nonneg` (v : L.D) : 0 ≤ (inner ℂ (v : F) (L.viscous v : F) : ℂ).re
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesLagrangianEsa`.
--
--   `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.viscous_nonneg` (v : L.D) : 0 ≤ (inner ℂ (v : F) (L.viscous v : F) : ℂ).re
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.viscous_nonneg`.

-- Generated from ChapterNavierStokesLagrangianEsa.lean — theorem BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.viscous_nonneg
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.BRSTNilpotent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa




open FullEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)

theorem BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.viscous_nonneg (v : L.D) : 0 ≤ (inner ℂ (v : F) (L.viscous v : F) : ℂ).re := by sorry
