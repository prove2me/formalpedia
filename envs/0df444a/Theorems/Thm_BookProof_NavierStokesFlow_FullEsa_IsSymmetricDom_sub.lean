-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_IsSymmetricDom_sub
-- name    : BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.sub
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T10:12:37.237464+00:00
-- url     : https://prove2.me/theorems/19274d6c-6f31-4461-96a0-61182217ce04
-- title:
--   `BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.sub` {A B : D →ₗ[ℂ] D} (hA : IsSymmetricDom A) (hB : IsSymmetricDom B) : IsSymmetricDom (A - B)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFullEsa`.
--
--   `BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.sub` {A B : D →ₗ[ℂ] D} (hA : IsSymmetricDom A) (hB : IsSymmetricDom B) : IsSymmetricDom (A - B)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.sub`.

-- Generated from ChapterNavierStokesFullEsa.lean — theorem BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.sub
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow


open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

theorem BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.sub {A B : D →ₗ[ℂ] D} (hA : IsSymmetricDom A) (hB : IsSymmetricDom B) :
    IsSymmetricDom (A - B) := by sorry
