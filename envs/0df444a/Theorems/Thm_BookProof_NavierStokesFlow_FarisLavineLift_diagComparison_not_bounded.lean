-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FarisLavineLift_diagComparison_not_bounded
-- name    : BookProof.NavierStokesFlow.FarisLavineLift.diagComparison_not_bounded
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:50:27.801816+00:00
-- url     : https://prove2.me/theorems/d31bb8c4-8910-4222-a289-d4f6e69b0539
-- title:
--   (d : ℕ) (p q : Fin d → ℕ → ℝ) (hunb : ∀ C : ℝ, ∃ k, C < |(∑ i, p i k ^ 2) + (∑ i, q i k ^ 2) + 1|) : ¬ ∃ C : ℝ, ∀ f : lpFiniteModes ℕ, ‖(diagComparisonData d p q).comparison f‖ ≤ C * ‖f‖
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FarisLavineLift.diagComparison_not_bounded` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFarisLavineLift.lean — theorem BookProof.NavierStokesFlow.FarisLavineLift.diagComparison_not_bounded
import Mathlib
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {d : ℕ} (c : ComparisonData F d)

theorem BookProof.NavierStokesFlow.FarisLavineLift.diagComparison_not_bounded (d : ℕ) (p q : Fin d → ℕ → ℝ)
    (hunb : ∀ C : ℝ, ∃ k, C < |(∑ i, p i k ^ 2) + (∑ i, q i k ^ 2) + 1|) :
    ¬ ∃ C : ℝ, ∀ f : lpFiniteModes ℕ,
      ‖(diagComparisonData d p q).comparison f‖ ≤ C * ‖f‖ := by sorry
