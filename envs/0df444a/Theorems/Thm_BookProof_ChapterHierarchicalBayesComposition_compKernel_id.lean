-- Prove2me | Theorems.Thm_BookProof_ChapterHierarchicalBayesComposition_compKernel_id
-- name    : BookProof.ChapterHierarchicalBayesComposition.compKernel_id
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:14:48.842311+00:00
-- url     : https://prove2.me/theorems/154d426d-66a3-4321-84e7-1c646e1bf0c9
-- title:
--   `BookProof.ChapterHierarchicalBayesComposition.compKernel_id` (k : A → B → ℝ) : compKernel k (idKernel : B → B → ℝ) = k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHierarchicalBayesComposition`.
--
--   `BookProof.ChapterHierarchicalBayesComposition.compKernel_id` (k : A → B → ℝ) : compKernel k (idKernel : B → B → ℝ) = k
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterHierarchicalBayesComposition.compKernel_id`.

-- Generated from ChapterHierarchicalBayesComposition.lean — theorem BookProof.ChapterHierarchicalBayesComposition.compKernel_id
import Mathlib
import Definitions.Def_ChapterHierarchicalBayesComposition
open BookProof.ChapterHierarchicalBayesComposition


open scoped BigOperators


variable {A B C D : Type*}
  [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

theorem BookProof.ChapterHierarchicalBayesComposition.compKernel_id (k : A → B → ℝ) :
    compKernel k (idKernel : B → B → ℝ) = k := by sorry
