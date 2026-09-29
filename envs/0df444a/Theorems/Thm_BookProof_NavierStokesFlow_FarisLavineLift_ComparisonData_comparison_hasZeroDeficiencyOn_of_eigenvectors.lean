-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FarisLavineLift_ComparisonData_comparison_hasZeroDeficiencyOn_of_eigenvectors
-- name    : BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData.comparison_hasZeroDeficiencyOn_of_eigenvectors
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:50:27.472573+00:00
-- url     : https://prove2.me/theorems/9d359184-9668-42e3-aee7-dc45375e55c0
-- title:
--   {I : Type*} (e : I → c.D) (lam : I → ℝ) (heig : ∀ i, c.comparison (e i) = ((lam i : ℂ)) • e i) (htotal : ∀ w : F, (∀ i, (inner ℂ ((e i : c.D) : F) w : ℂ) = 0) → w = 0) : HasZeroDeficiencyOn c.D...
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData.comparison_hasZeroDeficiencyOn_of_eigenvectors` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFarisLavineLift.lean — theorem BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData.comparison_hasZeroDeficiencyOn_of_eigenvectors
import Mathlib
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift
open BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {d : ℕ} (c : ComparisonData F d)

theorem BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData.comparison_hasZeroDeficiencyOn_of_eigenvectors {I : Type*} (e : I → c.D) (lam : I → ℝ)
    (heig : ∀ i, c.comparison (e i) = ((lam i : ℂ)) • e i)
    (htotal : ∀ w : F, (∀ i, (inner ℂ ((e i : c.D) : F) w : ℂ) = 0) → w = 0) :
    HasZeroDeficiencyOn c.D c.comparison := by sorry
