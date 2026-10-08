-- Prove2me | Theorems.Thm_BookProof_ChapterBayesInference_joint_sum_one
-- name    : BookProof.ChapterBayesInference.joint_sum_one
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:52:47.703873+00:00
-- url     : https://prove2.me/theorems/50977112-2490-4ea2-9602-273543890a27
-- title:
--   `BookProof.ChapterBayesInference.joint_sum_one` (hprior_sum : ∑ x, prior x = 1) (hL_row : ∀ x, ∑ y, L x y = 1) : ∑ x, ∑ y, joint prior L x y = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBayesInference`.
--
--   `BookProof.ChapterBayesInference.joint_sum_one` (hprior_sum : ∑ x, prior x = 1) (hL_row : ∀ x, ∑ y, L x y = 1) : ∑ x, ∑ y, joint prior L x y = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterBayesInference.joint_sum_one`.

-- Generated from ChapterBayesInference.lean — theorem BookProof.ChapterBayesInference.joint_sum_one
import Mathlib
import Definitions.Def_ChapterBayesInference
open BookProof.ChapterBayesInference


open scoped BigOperators


variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

variable {prior : X → ℝ} {L : X → Y → ℝ}

omit [DecidableEq X] [DecidableEq Y] in

theorem BookProof.ChapterBayesInference.joint_sum_one (hprior_sum : ∑ x, prior x = 1) (hL_row : ∀ x, ∑ y, L x y = 1) :
    ∑ x, ∑ y, joint prior L x y = 1 := by sorry
