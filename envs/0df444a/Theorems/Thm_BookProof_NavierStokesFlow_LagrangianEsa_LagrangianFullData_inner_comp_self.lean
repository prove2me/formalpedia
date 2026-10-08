-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_LagrangianFullData_inner_comp_self
-- name    : BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.inner_comp_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T11:53:10.133992+00:00
-- url     : https://prove2.me/theorems/a5bd7e8e-b676-47f2-9e5b-8c78e4714212
-- title:
--   `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.inner_comp_self` {D : Submodule ℂ F} {A : D →ₗ[ℂ] D} (hA : IsSymmetricDom A) (v : D) : (inner ℂ (v : F) ((A.comp A) v :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesLagrangianEsa`.
--
--   `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.inner_comp_self` {D : Submodule ℂ F} {A : D →ₗ[ℂ] D} (hA : IsSymmetricDom A) (v : D) : (inner ℂ (v : F) ((A.comp A) v : F) : ℂ) = ((‖(A v : F)‖ ^ 2 : ℝ) : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.inner_comp_self`.

-- Generated from ChapterNavierStokesLagrangianEsa.lean — theorem BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.inner_comp_self
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

theorem BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.inner_comp_self {D : Submodule ℂ F} {A : D →ₗ[ℂ] D} (hA : IsSymmetricDom A) (v : D) :
    (inner ℂ (v : F) ((A.comp A) v : F) : ℂ) = ((‖(A v : F)‖ ^ 2 : ℝ) : ℂ) := by sorry
