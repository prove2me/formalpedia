-- Prove2me | Theorems.Thm_BookProof_ChapterFiniteBayesHierarchy_nestedMarginal_eq_terminalMarginal
-- name    : BookProof.ChapterFiniteBayesHierarchy.nestedMarginal_eq_terminalMarginal
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T10:20:53.877983+00:00
-- url     : https://prove2.me/theorems/2c948202-4965-43e1-ac6c-33d721ccfec0
-- title:
--   `BookProof.ChapterFiniteBayesHierarchy.nestedMarginal_eq_terminalMarginal` (ks : List (S → S → ℝ)) (likelihood : S → ℝ) : nestedMarginal ks likelihood = terminalMarginal (collapseK
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFiniteBayesHierarchy`.
--
--   `BookProof.ChapterFiniteBayesHierarchy.nestedMarginal_eq_terminalMarginal` (ks : List (S → S → ℝ)) (likelihood : S → ℝ) : nestedMarginal ks likelihood = terminalMarginal (collapseKernels ks) likelihood
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFiniteBayesHierarchy.nestedMarginal_eq_terminalMarginal`.

-- Generated from ChapterFiniteBayesHierarchy.lean — theorem BookProof.ChapterFiniteBayesHierarchy.nestedMarginal_eq_terminalMarginal
import Mathlib
import Definitions.Def_ChapterFiniteBayesHierarchy
import Definitions.Def_ChapterHierarchicalBayesComposition
open BookProof.ChapterHierarchicalBayesComposition
open BookProof.ChapterFiniteBayesHierarchy


open scoped BigOperators


open BookProof.ChapterHierarchicalBayesComposition

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem BookProof.ChapterFiniteBayesHierarchy.nestedMarginal_eq_terminalMarginal (ks : List (S → S → ℝ))
    (likelihood : S → ℝ) :
    nestedMarginal ks likelihood =
      terminalMarginal (collapseKernels ks) likelihood := by sorry
