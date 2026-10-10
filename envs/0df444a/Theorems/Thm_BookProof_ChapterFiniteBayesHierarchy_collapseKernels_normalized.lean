-- Prove2me | Theorems.Thm_BookProof_ChapterFiniteBayesHierarchy_collapseKernels_normalized
-- name    : BookProof.ChapterFiniteBayesHierarchy.collapseKernels_normalized
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T10:19:53.668339+00:00
-- url     : https://prove2.me/theorems/ba9c5e5d-f96c-41bb-beca-56feacf5b328
-- title:
--   `BookProof.ChapterFiniteBayesHierarchy.collapseKernels_normalized` (ks : List (S → S → ℝ)) (hks : ∀ k ∈ ks, IsNormalizedKernel k) : IsNormalizedKernel (collapseKernels ks)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFiniteBayesHierarchy`.
--
--   `BookProof.ChapterFiniteBayesHierarchy.collapseKernels_normalized` (ks : List (S → S → ℝ)) (hks : ∀ k ∈ ks, IsNormalizedKernel k) : IsNormalizedKernel (collapseKernels ks)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFiniteBayesHierarchy.collapseKernels_normalized`.

-- Generated from ChapterFiniteBayesHierarchy.lean — theorem BookProof.ChapterFiniteBayesHierarchy.collapseKernels_normalized
import Mathlib
import Definitions.Def_ChapterFiniteBayesHierarchy
import Definitions.Def_ChapterHierarchicalBayesComposition
open BookProof.ChapterHierarchicalBayesComposition
open BookProof.ChapterFiniteBayesHierarchy


open scoped BigOperators


open BookProof.ChapterHierarchicalBayesComposition

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem BookProof.ChapterFiniteBayesHierarchy.collapseKernels_normalized (ks : List (S → S → ℝ))
    (hks : ∀ k ∈ ks, IsNormalizedKernel k) :
    IsNormalizedKernel (collapseKernels ks) := by sorry
