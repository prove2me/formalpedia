-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_IsSymmetricDom_comp_of_commute
-- name    : BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.comp_of_commute
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T11:53:55.147979+00:00
-- url     : https://prove2.me/theorems/3c985152-2ea2-4447-a538-e89938c9e945
-- title:
--   `BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.comp_of_commute` {A B : D →ₗ[ℂ] D} (hA : IsSymmetricDom A) (hB : IsSymmetricDom B) (hcomm : A.comp B = B.comp A) : IsSymmetricDom
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFullEsa`.
--
--   `BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.comp_of_commute` {A B : D →ₗ[ℂ] D} (hA : IsSymmetricDom A) (hB : IsSymmetricDom B) (hcomm : A.comp B = B.comp A) : IsSymmetricDom (A.comp B)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.comp_of_commute`.

-- Generated from ChapterNavierStokesFullEsa.lean — theorem BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.comp_of_commute
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow


open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

theorem BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.comp_of_commute {A B : D →ₗ[ℂ] D} (hA : IsSymmetricDom A)
    (hB : IsSymmetricDom B) (hcomm : A.comp B = B.comp A) : IsSymmetricDom (A.comp B) := by sorry
