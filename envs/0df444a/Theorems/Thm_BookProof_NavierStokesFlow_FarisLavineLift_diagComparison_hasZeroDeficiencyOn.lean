-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FarisLavineLift_diagComparison_hasZeroDeficiencyOn
-- name    : BookProof.NavierStokesFlow.FarisLavineLift.diagComparison_hasZeroDeficiencyOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:49:50.86253+00:00
-- url     : https://prove2.me/theorems/3a937f74-f23e-4a32-b624-0b962392b8be
-- title:
--   (d : ℕ) (p q : Fin d → ℕ → ℝ) : HasZeroDeficiencyOn (lpFiniteModes ℕ) (diagComparisonData d p q).comparison
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FarisLavineLift.diagComparison_hasZeroDeficiencyOn` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFarisLavineLift.lean — theorem BookProof.NavierStokesFlow.FarisLavineLift.diagComparison_hasZeroDeficiencyOn
import Mathlib
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {d : ℕ} (c : ComparisonData F d)

theorem BookProof.NavierStokesFlow.FarisLavineLift.diagComparison_hasZeroDeficiencyOn (d : ℕ) (p q : Fin d → ℕ → ℝ) :
    HasZeroDeficiencyOn (lpFiniteModes ℕ) (diagComparisonData d p q).comparison := by sorry
