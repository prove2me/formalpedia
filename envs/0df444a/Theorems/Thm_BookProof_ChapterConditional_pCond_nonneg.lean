-- Prove2me | Theorems.Thm_BookProof_ChapterConditional_pCond_nonneg
-- name    : BookProof.ChapterConditional.pCond_nonneg
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:22:20.152129+00:00
-- url     : https://prove2.me/theorems/bf536cb5-8f91-4938-9836-fb7b7d1bb1f2
-- title:
--   `BookProof.ChapterConditional.pCond_nonneg` (B : Matrix Y X 𝕜) (x : X) (y : Y) : 0 ≤ pCond B x y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterConditional`.
--
--   `BookProof.ChapterConditional.pCond_nonneg` (B : Matrix Y X 𝕜) (x : X) (y : Y) : 0 ≤ pCond B x y
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterConditional.pCond_nonneg`.

-- Generated from ChapterConditional.lean — theorem BookProof.ChapterConditional.pCond_nonneg
import Mathlib
import Definitions.Def_ChapterConditional
open BookProof.ChapterConditional


open scoped BigOperators Matrix
open Finset


variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
variable {𝕜 : Type*} [RCLike 𝕜]


omit [Fintype X] [DecidableEq X] in

theorem BookProof.ChapterConditional.pCond_nonneg (B : Matrix Y X 𝕜) (x : X) (y : Y) : 0 ≤ pCond B x y := by sorry
