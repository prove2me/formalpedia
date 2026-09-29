-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_eq_zero_of_inner_right_eq_zero_on_dense
-- name    : BookProof.NavierStokesFlow.eq_zero_of_inner_right_eq_zero_on_dense
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:57:40.407825+00:00
-- url     : https://prove2.me/theorems/702a22af-7a58-4b7a-8cb9-61ed7712e13a
-- title:
--   The Lean 4 theorem `eq_zero_of_inner_right_eq_zero_on_dense` in the `ChapterNavierStokesEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `eq_zero_of_inner_right_eq_zero_on_dense` in the `ChapterNavierStokesEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesEsa.lean

-- Generated from ChapterNavierStokesEsa.lean — theorem BookProof.NavierStokesFlow.eq_zero_of_inner_right_eq_zero_on_dense
import Mathlib
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.NavierStokesFlow








open scoped Matrix



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.NavierStokesFlow.eq_zero_of_inner_right_eq_zero_on_dense {D : Submodule ℂ F} (hdense : Dense (D : Set F))
    (w : F) (hw : ∀ v : D, (inner ℂ w (v : F) : ℂ) = 0) : w = 0 := by sorry
