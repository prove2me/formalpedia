-- Prove2me | Theorems.Thm_BookProof_ChapterFiniteBayesHierarchy_collapseKernels_nonnegative
-- name    : BookProof.ChapterFiniteBayesHierarchy.collapseKernels_nonnegative
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T10:20:24.81799+00:00
-- url     : https://prove2.me/theorems/5211cd6e-b4f6-42eb-ad09-cab0029c6ac4
-- title:
--   `BookProof.ChapterFiniteBayesHierarchy.collapseKernels_nonnegative` (ks : List (S → S → ℝ)) (hks : ∀ k ∈ ks, IsNonnegativeKernel k) : IsNonnegativeKernel (collapseKernels ks)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFiniteBayesHierarchy`.
--
--   `BookProof.ChapterFiniteBayesHierarchy.collapseKernels_nonnegative` (ks : List (S → S → ℝ)) (hks : ∀ k ∈ ks, IsNonnegativeKernel k) : IsNonnegativeKernel (collapseKernels ks)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFiniteBayesHierarchy.collapseKernels_nonnegative`.

-- Generated from ChapterFiniteBayesHierarchy.lean — theorem BookProof.ChapterFiniteBayesHierarchy.collapseKernels_nonnegative
import Mathlib
import Definitions.Def_ChapterFiniteBayesHierarchy
import Definitions.Def_ChapterHierarchicalBayesComposition
open BookProof.ChapterHierarchicalBayesComposition
open BookProof.ChapterFiniteBayesHierarchy


open scoped BigOperators


open BookProof.ChapterHierarchicalBayesComposition

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem BookProof.ChapterFiniteBayesHierarchy.collapseKernels_nonnegative (ks : List (S → S → ℝ))
    (hks : ∀ k ∈ ks, IsNonnegativeKernel k) :
    IsNonnegativeKernel (collapseKernels ks) := by sorry
