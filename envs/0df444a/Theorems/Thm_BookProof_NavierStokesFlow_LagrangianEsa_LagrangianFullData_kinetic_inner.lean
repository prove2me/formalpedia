-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_LagrangianFullData_kinetic_inner
-- name    : BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.kinetic_inner
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T08:32:20.480992+00:00
-- url     : https://prove2.me/theorems/1654b3c8-cd6b-4633-a96d-9ad632b04eed
-- title:
--   `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.kinetic_inner` (v : L.D) : (inner ℂ (v : F) (L.kinetic v : F) : ℂ) = (((1 / 2 : ℝ) * ∑ i : Fin 3, ‖(L.P i v : F)‖ ^ 2 :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesLagrangianEsa`.
--
--   `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.kinetic_inner` (v : L.D) : (inner ℂ (v : F) (L.kinetic v : F) : ℂ) = (((1 / 2 : ℝ) * ∑ i : Fin 3, ‖(L.P i v : F)‖ ^ 2 : ℝ) : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.kinetic_inner`.

-- Generated from ChapterNavierStokesLagrangianEsa.lean — theorem BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.kinetic_inner
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

theorem BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.kinetic_inner (v : L.D) :
    (inner ℂ (v : F) (L.kinetic v : F) : ℂ)
      = (((1 / 2 : ℝ) * ∑ i : Fin 3, ‖(L.P i v : F)‖ ^ 2 : ℝ) : ℂ) := by sorry
