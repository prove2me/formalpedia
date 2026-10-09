-- Prove2me | Theorems.Thm_BookProof_ChapterConditional_pJoint_eq_cond_mul_marg
-- name    : BookProof.ChapterConditional.pJoint_eq_cond_mul_marg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:23:10.134173+00:00
-- url     : https://prove2.me/theorems/ffaa60ff-7309-41c8-8fb8-33664bd92111
-- title:
--   `BookProof.ChapterConditional.pJoint_eq_cond_mul_marg` (B : Matrix Y X 𝕜) (x : X) (y : Y) (hx : 0 < pMarg B x) : pJoint B x y = pCond B x y * pMarg B x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterConditional`.
--
--   `BookProof.ChapterConditional.pJoint_eq_cond_mul_marg` (B : Matrix Y X 𝕜) (x : X) (y : Y) (hx : 0 < pMarg B x) : pJoint B x y = pCond B x y * pMarg B x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterConditional.pJoint_eq_cond_mul_marg`.

-- Generated from ChapterConditional.lean — theorem BookProof.ChapterConditional.pJoint_eq_cond_mul_marg
import Mathlib
import Definitions.Def_ChapterConditional
open BookProof.ChapterConditional


open scoped BigOperators Matrix
open Finset


variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
variable {𝕜 : Type*} [RCLike 𝕜]

theorem BookProof.ChapterConditional.pJoint_eq_cond_mul_marg (B : Matrix Y X 𝕜) (x : X) (y : Y)
    (hx : 0 < pMarg B x) :
    pJoint B x y = pCond B x y * pMarg B x := by sorry
