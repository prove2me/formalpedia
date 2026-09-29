-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FarisLavineLift_ComparisonData_comparison_inner_eq
-- name    : BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData.comparison_inner_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:46:36.364498+00:00
-- url     : https://prove2.me/theorems/092f49b3-174d-4bf7-9b83-1cac78605e73
-- title:
--   (v : c.D) : (inner ℂ ((v : F)) ((c.comparison v : c.D) : F) : ℂ).re = (∑ i, ‖((c.mom i v : c.D) : F)‖ ^ 2) + (∑ i, ‖((c.drift i v : c.D) : F)‖ ^ 2) + ‖(v : F)‖ ^ 2
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData.comparison_inner_eq` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFarisLavineLift.lean — theorem BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData.comparison_inner_eq
import Mathlib
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift
open BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {d : ℕ} (c : ComparisonData F d)

theorem BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData.comparison_inner_eq (v : c.D) :
    (inner ℂ ((v : F)) ((c.comparison v : c.D) : F) : ℂ).re
      = (∑ i, ‖((c.mom i v : c.D) : F)‖ ^ 2) + (∑ i, ‖((c.drift i v : c.D) : F)‖ ^ 2)
        + ‖(v : F)‖ ^ 2 := by sorry
