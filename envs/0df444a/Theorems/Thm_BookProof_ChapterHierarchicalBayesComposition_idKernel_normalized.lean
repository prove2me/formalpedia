-- Prove2me | Theorems.Thm_BookProof_ChapterHierarchicalBayesComposition_idKernel_normalized
-- name    : BookProof.ChapterHierarchicalBayesComposition.idKernel_normalized
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:14:25.088082+00:00
-- url     : https://prove2.me/theorems/3d5d5f1c-1c15-496b-b064-eddf32ce6a48
-- title:
--   `BookProof.ChapterHierarchicalBayesComposition.idKernel_normalized` : IsNormalizedKernel (idKernel : A → A → ℝ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHierarchicalBayesComposition`.
--
--   `BookProof.ChapterHierarchicalBayesComposition.idKernel_normalized` : IsNormalizedKernel (idKernel : A → A → ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterHierarchicalBayesComposition.idKernel_normalized`.

-- Generated from ChapterHierarchicalBayesComposition.lean — theorem BookProof.ChapterHierarchicalBayesComposition.idKernel_normalized
import Mathlib
import Definitions.Def_ChapterHierarchicalBayesComposition
open BookProof.ChapterHierarchicalBayesComposition


open scoped BigOperators


variable {A B C D : Type*}
  [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

theorem BookProof.ChapterHierarchicalBayesComposition.idKernel_normalized : IsNormalizedKernel (idKernel : A → A → ℝ) := by sorry
