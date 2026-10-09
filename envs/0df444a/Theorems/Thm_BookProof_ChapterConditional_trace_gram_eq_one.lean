-- Prove2me | Theorems.Thm_BookProof_ChapterConditional_trace_gram_eq_one
-- name    : BookProof.ChapterConditional.trace_gram_eq_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:21:22.168901+00:00
-- url     : https://prove2.me/theorems/6644611c-aa89-4971-8ad4-b9abc65dab5d
-- title:
--   `BookProof.ChapterConditional.trace_gram_eq_one` (B : Matrix Y X 𝕜) (hB : ∑ x, ∑ y, ‖B y x‖ ^ 2 = 1) : (Bᴴ * B).trace = ((1 : ℝ) : 𝕜)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterConditional`.
--
--   `BookProof.ChapterConditional.trace_gram_eq_one` (B : Matrix Y X 𝕜) (hB : ∑ x, ∑ y, ‖B y x‖ ^ 2 = 1) : (Bᴴ * B).trace = ((1 : ℝ) : 𝕜)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterConditional.trace_gram_eq_one`.

-- Generated from ChapterConditional.lean — theorem BookProof.ChapterConditional.trace_gram_eq_one
import Mathlib
import Definitions.Def_ChapterConditional
open BookProof.ChapterConditional


open scoped BigOperators Matrix
open Finset


variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
variable {𝕜 : Type*} [RCLike 𝕜]

theorem BookProof.ChapterConditional.trace_gram_eq_one (B : Matrix Y X 𝕜)
    (hB : ∑ x, ∑ y, ‖B y x‖ ^ 2 = 1) :
    (Bᴴ * B).trace = ((1 : ℝ) : 𝕜) := by sorry
