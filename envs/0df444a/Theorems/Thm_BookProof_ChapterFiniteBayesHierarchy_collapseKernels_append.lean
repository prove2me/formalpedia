-- Prove2me | Theorems.Thm_BookProof_ChapterFiniteBayesHierarchy_collapseKernels_append
-- name    : BookProof.ChapterFiniteBayesHierarchy.collapseKernels_append
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T10:19:46.002463+00:00
-- url     : https://prove2.me/theorems/365e6379-b443-49d6-bcfe-29b3f1214f75
-- title:
--   `BookProof.ChapterFiniteBayesHierarchy.collapseKernels_append` (ks₁ ks₂ : List (S → S → ℝ)) : collapseKernels (ks₁ ++ ks₂) = compKernel (collapseKernels ks₁) (collapseKernels ks₂)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFiniteBayesHierarchy`.
--
--   `BookProof.ChapterFiniteBayesHierarchy.collapseKernels_append` (ks₁ ks₂ : List (S → S → ℝ)) : collapseKernels (ks₁ ++ ks₂) = compKernel (collapseKernels ks₁) (collapseKernels ks₂)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFiniteBayesHierarchy.collapseKernels_append`.

-- Generated from ChapterFiniteBayesHierarchy.lean — theorem BookProof.ChapterFiniteBayesHierarchy.collapseKernels_append
import Mathlib
import Definitions.Def_ChapterFiniteBayesHierarchy
import Definitions.Def_ChapterHierarchicalBayesComposition
open BookProof.ChapterHierarchicalBayesComposition
open BookProof.ChapterFiniteBayesHierarchy


open scoped BigOperators


open BookProof.ChapterHierarchicalBayesComposition

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem BookProof.ChapterFiniteBayesHierarchy.collapseKernels_append (ks₁ ks₂ : List (S → S → ℝ)) :
    collapseKernels (ks₁ ++ ks₂) =
      compKernel (collapseKernels ks₁) (collapseKernels ks₂) := by sorry
