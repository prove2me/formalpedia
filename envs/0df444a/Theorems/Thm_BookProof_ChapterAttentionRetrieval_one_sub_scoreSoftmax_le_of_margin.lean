-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionRetrieval_one_sub_scoreSoftmax_le_of_margin
-- name    : BookProof.ChapterAttentionRetrieval.one_sub_scoreSoftmax_le_of_margin
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:43:12.398903+00:00
-- url     : https://prove2.me/theorems/7581214b-1ab6-422e-a291-158085e565a7
-- title:
--   `BookProof.ChapterAttentionRetrieval.one_sub_scoreSoftmax_le_of_margin` {beta delta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ) (j : Fin m) (hmargin : ∀ l, l ≠ j → s l + delta ≤ s j) : 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionRetrieval`.
--
--   `BookProof.ChapterAttentionRetrieval.one_sub_scoreSoftmax_le_of_margin` {beta delta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ) (j : Fin m) (hmargin : ∀ l, l ≠ j → s l + delta ≤ s j) : 1 - scoreSoftmax beta s j ≤ ((m : ℝ) - 1) * Real.exp (-(beta * delta))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionRetrieval.one_sub_scoreSoftmax_le_of_margin`.

-- Generated from ChapterAttentionRetrieval.lean — theorem BookProof.ChapterAttentionRetrieval.one_sub_scoreSoftmax_le_of_margin
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

theorem BookProof.ChapterAttentionRetrieval.one_sub_scoreSoftmax_le_of_margin {beta delta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ)
    (j : Fin m) (hmargin : ∀ l, l ≠ j → s l + delta ≤ s j) :
    1 - scoreSoftmax beta s j ≤ ((m : ℝ) - 1) * Real.exp (-(beta * delta)) := by sorry
