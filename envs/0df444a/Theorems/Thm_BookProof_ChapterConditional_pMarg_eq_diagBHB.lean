-- Prove2me | Theorems.Thm_BookProof_ChapterConditional_pMarg_eq_diagBHB
-- name    : BookProof.ChapterConditional.pMarg_eq_diagBHB
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:18:48.892409+00:00
-- url     : https://prove2.me/theorems/162c9d56-b471-4779-b7a5-4d0a86deaaa6
-- title:
--   `BookProof.ChapterConditional.pMarg_eq_diagBHB` (B : Matrix Y X 𝕜) (x : X) : ((Bᴴ * B) x x) = ((pMarg B x : ℝ) : 𝕜)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterConditional`.
--
--   `BookProof.ChapterConditional.pMarg_eq_diagBHB` (B : Matrix Y X 𝕜) (x : X) : ((Bᴴ * B) x x) = ((pMarg B x : ℝ) : 𝕜)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterConditional.pMarg_eq_diagBHB`.

-- Generated from ChapterConditional.lean — theorem BookProof.ChapterConditional.pMarg_eq_diagBHB
import Mathlib
import Definitions.Def_ChapterConditional
open BookProof.ChapterConditional


open scoped BigOperators Matrix
open Finset


variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
variable {𝕜 : Type*} [RCLike 𝕜]

theorem BookProof.ChapterConditional.pMarg_eq_diagBHB (B : Matrix Y X 𝕜) (x : X) :
    ((Bᴴ * B) x x) = ((pMarg B x : ℝ) : 𝕜) := by sorry
