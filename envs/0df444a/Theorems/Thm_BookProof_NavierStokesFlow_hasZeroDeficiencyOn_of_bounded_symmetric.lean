-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_hasZeroDeficiencyOn_of_bounded_symmetric
-- name    : BookProof.NavierStokesFlow.hasZeroDeficiencyOn_of_bounded_symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:20:28.158561+00:00
-- url     : https://prove2.me/theorems/c00cb340-4509-4aaf-8a68-2387a37e839c
-- title:
--   The Lean 4 theorem `hasZeroDeficiencyOn_of_bounded_symmetric` in the `ChapterNavierStokesEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hasZeroDeficiencyOn_of_bounded_symmetric` in the `ChapterNavierStokesEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesEsa.lean

-- Generated from ChapterNavierStokesEsa.lean — theorem BookProof.NavierStokesFlow.hasZeroDeficiencyOn_of_bounded_symmetric
import Mathlib
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.NavierStokesFlow








open scoped Matrix



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.NavierStokesFlow.hasZeroDeficiencyOn_of_bounded_symmetric (A : F →L[ℂ] F)
    (hsym : (A : F →ₗ[ℂ] F).IsSymmetric) (D : Submodule ℂ F) (hdense : Dense (D : Set F))
    (hinv : ∀ v : D, A (v : F) ∈ D) :
    HasZeroDeficiencyOn D
      (LinearMap.codRestrict D ((A : F →ₗ[ℂ] F).comp D.subtype) fun v => hinv v) := by sorry
