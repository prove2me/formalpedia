-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_LagrangianFullData_hasZeroDeficiencyOn_of_boundedRealization
-- name    : BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hasZeroDeficiencyOn_of_boundedRealization
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T11:53:31.326987+00:00
-- url     : https://prove2.me/theorems/0418221d-b8fa-4d8e-b11e-ecbe39687c17
-- title:
--   `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hasZeroDeficiencyOn_of_boundedRealization` (A : F →L[ℂ] F) (hsym : (A : F →ₗ[ℂ] F).IsSymmetric) (hHA : ∀ x : L.D, (L.hF
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesLagrangianEsa`.
--
--   `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hasZeroDeficiencyOn_of_boundedRealization` (A : F →L[ℂ] F) (hsym : (A : F →ₗ[ℂ] F).IsSymmetric) (hHA : ∀ x : L.D, (L.hFull x : F) = A (x : F)) : HasZeroDeficiencyOn L.D L.hFull
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hasZeroDeficiencyOn_of_boundedRealization`.

-- Generated from ChapterNavierStokesLagrangianEsa.lean — theorem BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hasZeroDeficiencyOn_of_boundedRealization
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa




open FullEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)

theorem BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hasZeroDeficiencyOn_of_boundedRealization (A : F →L[ℂ] F)
    (hsym : (A : F →ₗ[ℂ] F).IsSymmetric) (hHA : ∀ x : L.D, (L.hFull x : F) = A (x : F)) :
    HasZeroDeficiencyOn L.D L.hFull := by sorry
