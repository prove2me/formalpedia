-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_hasZeroDeficiencyOn_of_boundedRealization
-- name    : BookProof.NavierStokesFlow.FullEsa.hasZeroDeficiencyOn_of_boundedRealization
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T11:52:17.678976+00:00
-- url     : https://prove2.me/theorems/0773c615-c4d6-4fd6-b365-0772e259b951
-- title:
--   `BookProof.NavierStokesFlow.FullEsa.hasZeroDeficiencyOn_of_boundedRealization` {D : Submodule ℂ F} (H : D →ₗ[ℂ] D) (A : F →L[ℂ] F) (hsym : (A : F →ₗ[ℂ] F).IsSymmetric) (hdense : De
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFullEsa`.
--
--   `BookProof.NavierStokesFlow.FullEsa.hasZeroDeficiencyOn_of_boundedRealization` {D : Submodule ℂ F} (H : D →ₗ[ℂ] D) (A : F →L[ℂ] F) (hsym : (A : F →ₗ[ℂ] F).IsSymmetric) (hdense : Dense (D : Set F)) (hHA : ∀ x : D, (H x : F) = A (x : F)) : HasZeroDeficiencyOn D H
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FullEsa.hasZeroDeficiencyOn_of_boundedRealization`.

-- Generated from ChapterNavierStokesFullEsa.lean — theorem BookProof.NavierStokesFlow.FullEsa.hasZeroDeficiencyOn_of_boundedRealization
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa


open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

theorem BookProof.NavierStokesFlow.FullEsa.hasZeroDeficiencyOn_of_boundedRealization {D : Submodule ℂ F} (H : D →ₗ[ℂ] D)
    (A : F →L[ℂ] F) (hsym : (A : F →ₗ[ℂ] F).IsSymmetric) (hdense : Dense (D : Set F))
    (hHA : ∀ x : D, (H x : F) = A (x : F)) : HasZeroDeficiencyOn D H := by sorry
