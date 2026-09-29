-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FarisLavineLift_ComparisonData_comparison_ge_norm_sq
-- name    : BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData.comparison_ge_norm_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:23:00.980383+00:00
-- url     : https://prove2.me/theorems/a2054040-26ec-47ba-ae17-f919e5e21eb9
-- title:
--   (v : c.D) : ‖(v : F)‖ ^ 2 ≤ (inner ℂ ((v : F)) ((c.comparison v : c.D) : F) : ℂ).re
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData.comparison_ge_norm_sq` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFarisLavineLift.lean — theorem BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData.comparison_ge_norm_sq
import Mathlib
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift
open BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {d : ℕ} (c : ComparisonData F d)

theorem BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData.comparison_ge_norm_sq (v : c.D) :
    ‖(v : F)‖ ^ 2 ≤ (inner ℂ ((v : F)) ((c.comparison v : c.D) : F) : ℂ).re := by sorry
