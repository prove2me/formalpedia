-- Prove2me | Theorems.Thm_BookProof_ChapterHierarchicalBayesComposition_idKernel_comp
-- name    : BookProof.ChapterHierarchicalBayesComposition.idKernel_comp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:15:20.168424+00:00
-- url     : https://prove2.me/theorems/66d3e795-c48c-4fae-999c-add49354b17f
-- title:
--   `BookProof.ChapterHierarchicalBayesComposition.idKernel_comp` (k : A → B → ℝ) : compKernel (idKernel : A → A → ℝ) k = k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHierarchicalBayesComposition`.
--
--   `BookProof.ChapterHierarchicalBayesComposition.idKernel_comp` (k : A → B → ℝ) : compKernel (idKernel : A → A → ℝ) k = k
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterHierarchicalBayesComposition.idKernel_comp`.

-- Generated from ChapterHierarchicalBayesComposition.lean — theorem BookProof.ChapterHierarchicalBayesComposition.idKernel_comp
import Mathlib
import Definitions.Def_ChapterHierarchicalBayesComposition
open BookProof.ChapterHierarchicalBayesComposition


open scoped BigOperators


variable {A B C D : Type*}
  [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

theorem BookProof.ChapterHierarchicalBayesComposition.idKernel_comp (k : A → B → ℝ) :
    compKernel (idKernel : A → A → ℝ) k = k := by sorry
