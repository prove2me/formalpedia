-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionRetrieval_scoreSoftmax_le_exp_neg_margin
-- name    : BookProof.ChapterAttentionRetrieval.scoreSoftmax_le_exp_neg_margin
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:42:48.293278+00:00
-- url     : https://prove2.me/theorems/a32989e8-268a-45db-a3f6-187401273645
-- title:
--   `BookProof.ChapterAttentionRetrieval.scoreSoftmax_le_exp_neg_margin` {beta delta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ) {j l : Fin m} (h : s l + delta ≤ s j) : scoreSoftmax beta s l
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionRetrieval`.
--
--   `BookProof.ChapterAttentionRetrieval.scoreSoftmax_le_exp_neg_margin` {beta delta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ) {j l : Fin m} (h : s l + delta ≤ s j) : scoreSoftmax beta s l ≤ Real.exp (-(beta * delta))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionRetrieval.scoreSoftmax_le_exp_neg_margin`.

-- Generated from ChapterAttentionRetrieval.lean — theorem BookProof.ChapterAttentionRetrieval.scoreSoftmax_le_exp_neg_margin
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

theorem BookProof.ChapterAttentionRetrieval.scoreSoftmax_le_exp_neg_margin {beta delta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ)
    {j l : Fin m} (h : s l + delta ≤ s j) :
    scoreSoftmax beta s l ≤ Real.exp (-(beta * delta)) := by sorry
