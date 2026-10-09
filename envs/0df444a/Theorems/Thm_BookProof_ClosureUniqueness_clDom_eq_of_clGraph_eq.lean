-- Prove2me | Theorems.Thm_BookProof_ClosureUniqueness_clDom_eq_of_clGraph_eq
-- name    : BookProof.ClosureUniqueness.clDom_eq_of_clGraph_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:42:18.163888+00:00
-- url     : https://prove2.me/theorems/b73cbcd2-67f7-4242-b66d-2201f95319da
-- title:
--   `BookProof.ClosureUniqueness.clDom_eq_of_clGraph_eq` {T₁ : D₁ →ₗ[ℂ] F} {T₂ : D₂ →ₗ[ℂ] F} (h : clGraph T₁ = clGraph T₂) : clDom T₁ = clDom T₂
-- statement:
--   Prove the following Lean 4 theorem from `ChapterClosureUniqueness`.
--
--   `BookProof.ClosureUniqueness.clDom_eq_of_clGraph_eq` {T₁ : D₁ →ₗ[ℂ] F} {T₂ : D₂ →ₗ[ℂ] F} (h : clGraph T₁ = clGraph T₂) : clDom T₁ = clDom T₂
--
--   Formalization note: Lean 4 identifier `BookProof.ClosureUniqueness.clDom_eq_of_clGraph_eq`.

-- Generated from ChapterClosureUniqueness.lean — theorem BookProof.ClosureUniqueness.clDom_eq_of_clGraph_eq
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
open BookProof.EsaClosure
open BookProof.ClosureUniqueness



open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

theorem BookProof.ClosureUniqueness.clDom_eq_of_clGraph_eq {T₁ : D₁ →ₗ[ℂ] F} {T₂ : D₂ →ₗ[ℂ] F}
    (h : clGraph T₁ = clGraph T₂) : clDom T₁ = clDom T₂ := by sorry
