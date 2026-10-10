-- Prove2me | Theorems.Thm_BookProof_ChapterHierarchicalBayesComposition_idKernel_nonnegative
-- name    : BookProof.ChapterHierarchicalBayesComposition.idKernel_nonnegative
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:14:34.448987+00:00
-- url     : https://prove2.me/theorems/ceb7a10c-f701-40e8-ba75-fa7b893a8402
-- title:
--   `BookProof.ChapterHierarchicalBayesComposition.idKernel_nonnegative` : IsNonnegativeKernel (idKernel : A → A → ℝ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHierarchicalBayesComposition`.
--
--   `BookProof.ChapterHierarchicalBayesComposition.idKernel_nonnegative` : IsNonnegativeKernel (idKernel : A → A → ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterHierarchicalBayesComposition.idKernel_nonnegative`.

-- Generated from ChapterHierarchicalBayesComposition.lean — theorem BookProof.ChapterHierarchicalBayesComposition.idKernel_nonnegative
import Mathlib
import Definitions.Def_ChapterHierarchicalBayesComposition
open BookProof.ChapterHierarchicalBayesComposition


open scoped BigOperators


variable {A B C D : Type*}
  [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

theorem BookProof.ChapterHierarchicalBayesComposition.idKernel_nonnegative : IsNonnegativeKernel (idKernel : A → A → ℝ) := by sorry
