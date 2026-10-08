-- Prove2me | Theorems.Thm_BookProof_ChapterConditional_pCond_sum_one
-- name    : BookProof.ChapterConditional.pCond_sum_one
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:22:23.403983+00:00
-- url     : https://prove2.me/theorems/6267b572-16c7-413d-a661-ca3d76f7f123
-- title:
--   `BookProof.ChapterConditional.pCond_sum_one` (B : Matrix Y X 𝕜) (x : X) (hx : 0 < pMarg B x) : ∑ y, pCond B x y = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterConditional`.
--
--   `BookProof.ChapterConditional.pCond_sum_one` (B : Matrix Y X 𝕜) (x : X) (hx : 0 < pMarg B x) : ∑ y, pCond B x y = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterConditional.pCond_sum_one`.

-- Generated from ChapterConditional.lean — theorem BookProof.ChapterConditional.pCond_sum_one
import Mathlib
import Definitions.Def_ChapterConditional
open BookProof.ChapterConditional


open scoped BigOperators Matrix
open Finset


variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
variable {𝕜 : Type*} [RCLike 𝕜]

theorem BookProof.ChapterConditional.pCond_sum_one (B : Matrix Y X 𝕜) (x : X) (hx : 0 < pMarg B x) :
    ∑ y, pCond B x y = 1 := by sorry
