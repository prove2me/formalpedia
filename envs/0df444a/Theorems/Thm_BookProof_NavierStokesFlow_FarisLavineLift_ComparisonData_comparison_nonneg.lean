-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FarisLavineLift_ComparisonData_comparison_nonneg
-- name    : BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData.comparison_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T14:20:13.534172+00:00
-- url     : https://prove2.me/theorems/df4e2004-782d-40b9-bb20-170b827093d6
-- title:
--   (v : c.D) : 0 ≤ (inner ℂ ((v : F)) ((c.comparison v : c.D) : F) : ℂ).re
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData.comparison_nonneg` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFarisLavineLift.lean — theorem BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData.comparison_nonneg
import Mathlib
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift
open BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {d : ℕ} (c : ComparisonData F d)

theorem BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData.comparison_nonneg (v : c.D) :
    0 ≤ (inner ℂ ((v : F)) ((c.comparison v : c.D) : F) : ℂ).re := by sorry
