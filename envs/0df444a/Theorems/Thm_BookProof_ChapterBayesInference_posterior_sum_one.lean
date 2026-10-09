-- Prove2me | Theorems.Thm_BookProof_ChapterBayesInference_posterior_sum_one
-- name    : BookProof.ChapterBayesInference.posterior_sum_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:53:38.962195+00:00
-- url     : https://prove2.me/theorems/5008e975-1f46-488b-8654-6537d38e6009
-- title:
--   `BookProof.ChapterBayesInference.posterior_sum_one` (y : Y) (hy : 0 < evidence prior L y) : ∑ x, posterior prior L y x = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBayesInference`.
--
--   `BookProof.ChapterBayesInference.posterior_sum_one` (y : Y) (hy : 0 < evidence prior L y) : ∑ x, posterior prior L y x = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterBayesInference.posterior_sum_one`.

-- Generated from ChapterBayesInference.lean — theorem BookProof.ChapterBayesInference.posterior_sum_one
import Mathlib
import Definitions.Def_ChapterBayesInference
open BookProof.ChapterBayesInference


open scoped BigOperators


variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

variable {prior : X → ℝ} {L : X → Y → ℝ}

theorem BookProof.ChapterBayesInference.posterior_sum_one (y : Y) (hy : 0 < evidence prior L y) :
    ∑ x, posterior prior L y x = 1 := by sorry
