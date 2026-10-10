-- Prove2me | Theorems.Thm_BookProof_ChapterHierarchicalBayesComposition_terminalMarginal_comp
-- name    : BookProof.ChapterHierarchicalBayesComposition.terminalMarginal_comp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:14:56.39978+00:00
-- url     : https://prove2.me/theorems/f05c2ce4-2c21-4af5-9794-41eabc3d1b9e
-- title:
--   `BookProof.ChapterHierarchicalBayesComposition.terminalMarginal_comp` (k₁ : A → B → ℝ) (k₂ : B → C → ℝ) (likelihood : C → ℝ) : terminalMarginal k₁ (terminalMarginal k₂...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHierarchicalBayesComposition`.
--
--   `BookProof.ChapterHierarchicalBayesComposition.terminalMarginal_comp` (k₁ : A → B → ℝ) (k₂ : B → C → ℝ) (likelihood : C → ℝ) : terminalMarginal k₁ (terminalMarginal k₂ likelihood) = terminalMarginal (compKernel k₁ k₂) likelihood
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterHierarchicalBayesComposition.terminalMarginal_comp`.

-- Generated from ChapterHierarchicalBayesComposition.lean — theorem BookProof.ChapterHierarchicalBayesComposition.terminalMarginal_comp
import Mathlib
import Definitions.Def_ChapterHierarchicalBayesComposition
open BookProof.ChapterHierarchicalBayesComposition


open scoped BigOperators


variable {A B C D : Type*}
  [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

theorem BookProof.ChapterHierarchicalBayesComposition.terminalMarginal_comp (k₁ : A → B → ℝ) (k₂ : B → C → ℝ)
    (likelihood : C → ℝ) :
    terminalMarginal k₁ (terminalMarginal k₂ likelihood) =
      terminalMarginal (compKernel k₁ k₂) likelihood := by sorry
