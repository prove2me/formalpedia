-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_hasZeroDeficiencyOn_of_total_eigenvectors
-- name    : BookProof.NavierStokesFlow.hasZeroDeficiencyOn_of_total_eigenvectors
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:57:37.005858+00:00
-- url     : https://prove2.me/theorems/20edce07-0491-459b-afc7-69c1640acf72
-- title:
--   The Lean 4 theorem `hasZeroDeficiencyOn_of_total_eigenvectors` in the `ChapterNavierStokesEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hasZeroDeficiencyOn_of_total_eigenvectors` in the `ChapterNavierStokesEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesEsa.lean

-- Generated from ChapterNavierStokesEsa.lean — theorem BookProof.NavierStokesFlow.hasZeroDeficiencyOn_of_total_eigenvectors
import Mathlib
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.NavierStokesFlow








open scoped Matrix



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.NavierStokesFlow.hasZeroDeficiencyOn_of_total_eigenvectors {I : Type*} (D : Submodule ℂ F) (H : D →ₗ[ℂ] D)
    (e : I → D) (lam : I → ℝ) (heig : ∀ i, H (e i) = ((lam i : ℂ)) • e i)
    (htotal : ∀ w : F, (∀ i, (inner ℂ ((e i : F)) w : ℂ) = 0) → w = 0) :
    HasZeroDeficiencyOn D H := by sorry
