-- Prove2me | Theorems.Thm_BookProof_ChapterConditional_pMarg_nonneg
-- name    : BookProof.ChapterConditional.pMarg_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:18:44.048516+00:00
-- url     : https://prove2.me/theorems/397b1174-188c-432e-9bf0-cba44a619df9
-- title:
--   `BookProof.ChapterConditional.pMarg_nonneg` (B : Matrix Y X 𝕜) (x : X) : 0 ≤ pMarg B x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterConditional`.
--
--   `BookProof.ChapterConditional.pMarg_nonneg` (B : Matrix Y X 𝕜) (x : X) : 0 ≤ pMarg B x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterConditional.pMarg_nonneg`.

-- Generated from ChapterConditional.lean — theorem BookProof.ChapterConditional.pMarg_nonneg
import Mathlib
import Definitions.Def_ChapterConditional
open BookProof.ChapterConditional


open scoped BigOperators Matrix
open Finset


variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
variable {𝕜 : Type*} [RCLike 𝕜]


omit [Fintype X] [DecidableEq X] in

theorem BookProof.ChapterConditional.pMarg_nonneg (B : Matrix Y X 𝕜) (x : X) : 0 ≤ pMarg B x := by sorry
