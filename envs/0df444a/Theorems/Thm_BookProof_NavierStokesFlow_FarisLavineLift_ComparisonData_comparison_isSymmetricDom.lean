-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FarisLavineLift_ComparisonData_comparison_isSymmetricDom
-- name    : BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData.comparison_isSymmetricDom
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:22:13.413401+00:00
-- url     : https://prove2.me/theorems/c90eea0a-37f1-4eb8-b95e-f7831bd5a100
-- title:
--   The Lean 4 theorem `comparison_isSymmetricDom` in the `ChapterNavierStokesFarisLavineLift` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `comparison_isSymmetricDom` in the `ChapterNavierStokesFarisLavineLift` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFarisLavineLift.lean

-- Generated from ChapterNavierStokesFarisLavineLift.lean — theorem BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData.comparison_isSymmetricDom
import Mathlib
import Definitions.Def_ChapterNavierStokesFarisLavineLift
import Definitions.Def_ChapterNavierStokesFullEsa
open BookProof.NavierStokesFlow.FullEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift
open BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {d : ℕ} (c : ComparisonData F d)

theorem BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData.comparison_isSymmetricDom : IsSymmetricDom c.comparison := by sorry
