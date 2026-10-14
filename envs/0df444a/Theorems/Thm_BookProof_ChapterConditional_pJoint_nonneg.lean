-- Prove2me | Theorems.Thm_BookProof_ChapterConditional_pJoint_nonneg
-- name    : BookProof.ChapterConditional.pJoint_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:14:51.90775+00:00
-- url     : https://prove2.me/theorems/c20c8ec7-94e0-4e96-89eb-bc06b1cd1eab
-- title:
--   `BookProof.ChapterConditional.pJoint_nonneg` (B : Matrix Y X 𝕜) (x : X) (y : Y) : 0 ≤ pJoint B x y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterConditional`.
--
--   `BookProof.ChapterConditional.pJoint_nonneg` (B : Matrix Y X 𝕜) (x : X) (y : Y) : 0 ≤ pJoint B x y
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterConditional.pJoint_nonneg`.

-- Generated from ChapterConditional.lean — theorem BookProof.ChapterConditional.pJoint_nonneg
import Mathlib
import Definitions.Def_ChapterConditional
open BookProof.ChapterConditional


open scoped BigOperators Matrix
open Finset


variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
variable {𝕜 : Type*} [RCLike 𝕜]

theorem BookProof.ChapterConditional.pJoint_nonneg (B : Matrix Y X 𝕜) (x : X) (y : Y) : 0 ≤ pJoint B x y := by sorry
