-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionRetrieval_scoreSoftmax_ge_of_spread
-- name    : BookProof.ChapterAttentionRetrieval.scoreSoftmax_ge_of_spread
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:44:06.301188+00:00
-- url     : https://prove2.me/theorems/0816ed51-0a31-44c3-b762-ed3ae16d28e6
-- title:
--   `BookProof.ChapterAttentionRetrieval.scoreSoftmax_ge_of_spread` {beta D : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ) (j : Fin m) (hD : ∀ l, s l ≤ s j + D) : Real.exp (-(beta * D)) / (m : ℝ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionRetrieval`.
--
--   `BookProof.ChapterAttentionRetrieval.scoreSoftmax_ge_of_spread` {beta D : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ) (j : Fin m) (hD : ∀ l, s l ≤ s j + D) : Real.exp (-(beta * D)) / (m : ℝ) ≤ scoreSoftmax beta s j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionRetrieval.scoreSoftmax_ge_of_spread`.

-- Generated from ChapterAttentionRetrieval.lean — theorem BookProof.ChapterAttentionRetrieval.scoreSoftmax_ge_of_spread
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionRetrieval
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionRetrieval


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionRetrieval.scoreSoftmax_ge_of_spread {beta D : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ)
    (j : Fin m) (hD : ∀ l, s l ≤ s j + D) :
    Real.exp (-(beta * D)) / (m : ℝ) ≤ scoreSoftmax beta s j := by sorry
