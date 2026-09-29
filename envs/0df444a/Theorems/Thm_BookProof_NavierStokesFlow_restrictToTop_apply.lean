-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_restrictToTop_apply
-- name    : BookProof.NavierStokesFlow.restrictToTop_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T11:53:29.346609+00:00
-- url     : https://prove2.me/theorems/95f43dac-a54a-46ba-ab07-64e873518dc8
-- title:
--   The Lean 4 theorem `restrictToTop_apply` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `restrictToTop_apply` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFlow.lean — theorem BookProof.NavierStokesFlow.restrictToTop_apply
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.NavierStokesFlow.restrictToTop_apply (H : F →ₗ[ℂ] F) (v : (⊤ : Submodule ℂ F)) :
    (restrictToTop H v : F) = H (v : F) := by sorry
