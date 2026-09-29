-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FarisLavineLift_diagComparison_eq
-- name    : BookProof.NavierStokesFlow.FarisLavineLift.diagComparison_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:23:09.960003+00:00
-- url     : https://prove2.me/theorems/a23bf35a-1af8-4a8b-9417-642bb1f10451
-- title:
--   The Lean 4 theorem `diagComparison_eq` in the `ChapterNavierStokesFarisLavineLift` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `diagComparison_eq` in the `ChapterNavierStokesFarisLavineLift` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFarisLavineLift.lean

-- Generated from ChapterNavierStokesFarisLavineLift.lean — theorem BookProof.NavierStokesFlow.FarisLavineLift.diagComparison_eq
import Mathlib
import Definitions.Def_ChapterNavierStokesFarisLavineLift
import Definitions.Def_ChapterNavierStokesDeficiency
open BookProof.NavierStokesFlow.DiagonalEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {d : ℕ} (c : ComparisonData F d)

theorem BookProof.NavierStokesFlow.FarisLavineLift.diagComparison_eq (d : ℕ) (p q : Fin d → ℕ → ℝ) :
    (diagComparisonData d p q).comparison
      = diagOp (fun k => (∑ i, p i k ^ 2) + (∑ i, q i k ^ 2) + 1) := by sorry
