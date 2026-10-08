-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_LagrangianFullData_isSymmetricDom_sq
-- name    : BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.isSymmetricDom_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T11:38:39.68684+00:00
-- url     : https://prove2.me/theorems/9a393b22-1c52-46fd-9b91-7d8216503bdc
-- title:
--   `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.isSymmetricDom_sq` {D : Submodule ℂ F} {A : D →ₗ[ℂ] D} (hA : IsSymmetricDom A) : IsSymmetricDom (A.comp A)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesLagrangianEsa`.
--
--   `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.isSymmetricDom_sq` {D : Submodule ℂ F} {A : D →ₗ[ℂ] D} (hA : IsSymmetricDom A) : IsSymmetricDom (A.comp A)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.isSymmetricDom_sq`.

-- Generated from ChapterNavierStokesLagrangianEsa.lean — theorem BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.isSymmetricDom_sq
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa.NSFullData
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa




open FullEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)

theorem BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.isSymmetricDom_sq {D : Submodule ℂ F} {A : D →ₗ[ℂ] D} (hA : IsSymmetricDom A) :
    IsSymmetricDom (A.comp A) := by sorry
