-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_eq_zero_of_inner_left_eq_zero_on_dense
-- name    : BookProof.NavierStokesFlow.eq_zero_of_inner_left_eq_zero_on_dense
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:12:12.300457+00:00
-- url     : https://prove2.me/theorems/4319eee4-dc46-4108-9a16-cab5d0061f3a
-- title:
--   The Lean 4 theorem `eq_zero_of_inner_left_eq_zero_on_dense` in the `ChapterNavierStokesEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `eq_zero_of_inner_left_eq_zero_on_dense` in the `ChapterNavierStokesEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesEsa.lean

-- Generated from ChapterNavierStokesEsa.lean — theorem BookProof.NavierStokesFlow.eq_zero_of_inner_left_eq_zero_on_dense
import Mathlib
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.NavierStokesFlow








open scoped Matrix



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.NavierStokesFlow.eq_zero_of_inner_left_eq_zero_on_dense {D : Submodule ℂ F} (hdense : Dense (D : Set F))
    (w : F) (hw : ∀ v : D, (inner ℂ (v : F) w : ℂ) = 0) : w = 0 := by sorry
