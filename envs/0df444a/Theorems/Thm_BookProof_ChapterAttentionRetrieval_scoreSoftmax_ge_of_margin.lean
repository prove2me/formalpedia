-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionRetrieval_scoreSoftmax_ge_of_margin
-- name    : BookProof.ChapterAttentionRetrieval.scoreSoftmax_ge_of_margin
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:43:32.673573+00:00
-- url     : https://prove2.me/theorems/0bbb322a-b735-4695-bc6a-b1360c8e54f5
-- title:
--   `BookProof.ChapterAttentionRetrieval.scoreSoftmax_ge_of_margin` {beta delta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ) (j : Fin m) (hmargin : ∀ l, l ≠ j → s l + delta ≤ s j) : 1 - ((m :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionRetrieval`.
--
--   `BookProof.ChapterAttentionRetrieval.scoreSoftmax_ge_of_margin` {beta delta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ) (j : Fin m) (hmargin : ∀ l, l ≠ j → s l + delta ≤ s j) : 1 - ((m : ℝ) - 1) * Real.exp (-(beta * delta)) ≤ scoreSoftmax beta s j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionRetrieval.scoreSoftmax_ge_of_margin`.

-- Generated from ChapterAttentionRetrieval.lean — theorem BookProof.ChapterAttentionRetrieval.scoreSoftmax_ge_of_margin
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

theorem BookProof.ChapterAttentionRetrieval.scoreSoftmax_ge_of_margin {beta delta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ)
    (j : Fin m) (hmargin : ∀ l, l ≠ j → s l + delta ≤ s j) :
    1 - ((m : ℝ) - 1) * Real.exp (-(beta * delta)) ≤ scoreSoftmax beta s j := by sorry
