-- Prove2me | Theorems.Thm_BookProof_ChapterConditional_pJoint_sum_one
-- name    : BookProof.ChapterConditional.pJoint_sum_one
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:21:26.989824+00:00
-- url     : https://prove2.me/theorems/f146d35f-0480-4218-ac93-a0abec9711a1
-- title:
--   `BookProof.ChapterConditional.pJoint_sum_one` (B : Matrix Y X 𝕜) (hB : ∑ x, ∑ y, ‖B y x‖ ^ 2 = 1) : ∑ x, ∑ y, pJoint B x y = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterConditional`.
--
--   `BookProof.ChapterConditional.pJoint_sum_one` (B : Matrix Y X 𝕜) (hB : ∑ x, ∑ y, ‖B y x‖ ^ 2 = 1) : ∑ x, ∑ y, pJoint B x y = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterConditional.pJoint_sum_one`.

-- Generated from ChapterConditional.lean — theorem BookProof.ChapterConditional.pJoint_sum_one
import Mathlib
import Definitions.Def_ChapterConditional
open BookProof.ChapterConditional


open scoped BigOperators Matrix
open Finset


variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
variable {𝕜 : Type*} [RCLike 𝕜]

theorem BookProof.ChapterConditional.pJoint_sum_one (B : Matrix Y X 𝕜)
    (hB : ∑ x, ∑ y, ‖B y x‖ ^ 2 = 1) :
    ∑ x, ∑ y, pJoint B x y = 1 := by sorry
