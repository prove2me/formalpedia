-- Prove2me | Theorems.Thm_BookProof_ChapterBayesInference_joint_nonneg
-- name    : BookProof.ChapterBayesInference.joint_nonneg
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:52:38.272671+00:00
-- url     : https://prove2.me/theorems/6d75c03c-eb35-43ae-97b0-b2cd3106268c
-- title:
--   `BookProof.ChapterBayesInference.joint_nonneg` (hprior : ∀ x, 0 ≤ prior x) (hL : ∀ x y, 0 ≤ L x y) (x : X) (y : Y) : 0 ≤ joint prior L x y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBayesInference`.
--
--   `BookProof.ChapterBayesInference.joint_nonneg` (hprior : ∀ x, 0 ≤ prior x) (hL : ∀ x y, 0 ≤ L x y) (x : X) (y : Y) : 0 ≤ joint prior L x y
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterBayesInference.joint_nonneg`.

-- Generated from ChapterBayesInference.lean — theorem BookProof.ChapterBayesInference.joint_nonneg
import Mathlib
import Definitions.Def_ChapterBayesInference
open BookProof.ChapterBayesInference


open scoped BigOperators


variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

variable {prior : X → ℝ} {L : X → Y → ℝ}

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in

theorem BookProof.ChapterBayesInference.joint_nonneg (hprior : ∀ x, 0 ≤ prior x) (hL : ∀ x y, 0 ≤ L x y)
    (x : X) (y : Y) : 0 ≤ joint prior L x y := by sorry
