-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_IsSymmetricDom_anticomm
-- name    : BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.anticomm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T11:52:13.293561+00:00
-- url     : https://prove2.me/theorems/ca9e9dd3-81c8-4019-a0df-bfc787ea4cf1
-- title:
--   `BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.anticomm` {A B : D →ₗ[ℂ] D} (hA : IsSymmetricDom A) (hB : IsSymmetricDom B) : IsSymmetricDom (A.comp B + B.comp A)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFullEsa`.
--
--   `BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.anticomm` {A B : D →ₗ[ℂ] D} (hA : IsSymmetricDom A) (hB : IsSymmetricDom B) : IsSymmetricDom (A.comp B + B.comp A)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.anticomm`.

-- Generated from ChapterNavierStokesFullEsa.lean — theorem BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.anticomm
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow


open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

theorem BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.anticomm {A B : D →ₗ[ℂ] D} (hA : IsSymmetricDom A)
    (hB : IsSymmetricDom B) : IsSymmetricDom (A.comp B + B.comp A) := by sorry
