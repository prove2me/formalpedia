-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_NSFullData_hasZeroDeficiencyOn_of_boundedRealization
-- name    : BookProof.NavierStokesFlow.FullEsa.NSFullData.hasZeroDeficiencyOn_of_boundedRealization
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T11:53:07.768564+00:00
-- url     : https://prove2.me/theorems/56b63593-a68e-4691-a90f-e0244bedb3c1
-- title:
--   `BookProof.NavierStokesFlow.FullEsa.NSFullData.hasZeroDeficiencyOn_of_boundedRealization` (A : F →L[ℂ] F) (hsym : (A : F →ₗ[ℂ] F).IsSymmetric) (hHA : ∀ x : d.D, (d.hamiltonian x :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFullEsa`.
--
--   `BookProof.NavierStokesFlow.FullEsa.NSFullData.hasZeroDeficiencyOn_of_boundedRealization` (A : F →L[ℂ] F) (hsym : (A : F →ₗ[ℂ] F).IsSymmetric) (hHA : ∀ x : d.D, (d.hamiltonian x : F) = A (x : F)) : HasZeroDeficiencyOn d.D d.hamiltonian
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FullEsa.NSFullData.hasZeroDeficiencyOn_of_boundedRealization`.

-- Generated from ChapterNavierStokesFullEsa.lean — theorem BookProof.NavierStokesFlow.FullEsa.NSFullData.hasZeroDeficiencyOn_of_boundedRealization
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa


open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable (d : NSFullData F)

theorem BookProof.NavierStokesFlow.FullEsa.NSFullData.hasZeroDeficiencyOn_of_boundedRealization (A : F →L[ℂ] F)
    (hsym : (A : F →ₗ[ℂ] F).IsSymmetric) (hHA : ∀ x : d.D, (d.hamiltonian x : F) = A (x : F)) :
    HasZeroDeficiencyOn d.D d.hamiltonian := by sorry
