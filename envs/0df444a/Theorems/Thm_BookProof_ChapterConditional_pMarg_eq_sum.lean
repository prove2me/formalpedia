-- Prove2me | Theorems.Thm_BookProof_ChapterConditional_pMarg_eq_sum
-- name    : BookProof.ChapterConditional.pMarg_eq_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:18:48.861436+00:00
-- url     : https://prove2.me/theorems/0065e332-e8d0-4698-b1c1-c3b52fc137a5
-- title:
--   `BookProof.ChapterConditional.pMarg_eq_sum` (B : Matrix Y X 𝕜) (x : X) : pMarg B x = ∑ y, pJoint B x y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterConditional`.
--
--   `BookProof.ChapterConditional.pMarg_eq_sum` (B : Matrix Y X 𝕜) (x : X) : pMarg B x = ∑ y, pJoint B x y
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterConditional.pMarg_eq_sum`.

-- Generated from ChapterConditional.lean — theorem BookProof.ChapterConditional.pMarg_eq_sum
import Mathlib
import Definitions.Def_ChapterConditional
open BookProof.ChapterConditional


open scoped BigOperators Matrix
open Finset


variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
variable {𝕜 : Type*} [RCLike 𝕜]


omit [Fintype X] [DecidableEq X] in

theorem BookProof.ChapterConditional.pMarg_eq_sum (B : Matrix Y X 𝕜) (x : X) :
    pMarg B x = ∑ y, pJoint B x y := by sorry
