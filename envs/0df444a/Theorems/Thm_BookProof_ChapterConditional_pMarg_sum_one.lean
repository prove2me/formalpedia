-- Prove2me | Theorems.Thm_BookProof_ChapterConditional_pMarg_sum_one
-- name    : BookProof.ChapterConditional.pMarg_sum_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:21:30.637158+00:00
-- url     : https://prove2.me/theorems/479c96de-ab0e-46cc-963f-f3a6a19cc577
-- title:
--   `BookProof.ChapterConditional.pMarg_sum_one` (B : Matrix Y X 𝕜) (hB : ∑ x, ∑ y, ‖B y x‖ ^ 2 = 1) : ∑ x, pMarg B x = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterConditional`.
--
--   `BookProof.ChapterConditional.pMarg_sum_one` (B : Matrix Y X 𝕜) (hB : ∑ x, ∑ y, ‖B y x‖ ^ 2 = 1) : ∑ x, pMarg B x = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterConditional.pMarg_sum_one`.

-- Generated from ChapterConditional.lean — theorem BookProof.ChapterConditional.pMarg_sum_one
import Mathlib
import Definitions.Def_ChapterConditional
open BookProof.ChapterConditional


open scoped BigOperators Matrix
open Finset


variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
variable {𝕜 : Type*} [RCLike 𝕜]

theorem BookProof.ChapterConditional.pMarg_sum_one (B : Matrix Y X 𝕜)
    (hB : ∑ x, ∑ y, ‖B y x‖ ^ 2 = 1) :
    ∑ x, pMarg B x = 1 := by sorry
