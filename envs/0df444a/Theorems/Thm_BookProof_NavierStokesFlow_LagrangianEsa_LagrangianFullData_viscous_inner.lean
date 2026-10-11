-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_LagrangianFullData_viscous_inner
-- name    : BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.viscous_inner
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T08:15:20.162289+00:00
-- url     : https://prove2.me/theorems/3ab849a1-d854-4300-b29a-0d49a0c5b079
-- title:
--   `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.viscous_inner` (v : L.D) : (inner ℂ (v : F) (L.viscous v : F) : ℂ) = ((L.nu * ∑ i : Fin 3, ‖(L.Q i v : F)‖ ^ 2 : ℝ) : ℂ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesLagrangianEsa`.
--
--   `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.viscous_inner` (v : L.D) : (inner ℂ (v : F) (L.viscous v : F) : ℂ) = ((L.nu * ∑ i : Fin 3, ‖(L.Q i v : F)‖ ^ 2 : ℝ) : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.viscous_inner`.

-- Generated from ChapterNavierStokesLagrangianEsa.lean — theorem BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.viscous_inner
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

theorem BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.viscous_inner (v : L.D) :
    (inner ℂ (v : F) (L.viscous v : F) : ℂ)
      = ((L.nu * ∑ i : Fin 3, ‖(L.Q i v : F)‖ ^ 2 : ℝ) : ℂ) := by sorry
