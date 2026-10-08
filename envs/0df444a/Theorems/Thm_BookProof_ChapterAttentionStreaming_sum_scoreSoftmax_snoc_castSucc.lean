-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionStreaming_sum_scoreSoftmax_snoc_castSucc
-- name    : BookProof.ChapterAttentionStreaming.sum_scoreSoftmax_snoc_castSucc
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:51:10.088685+00:00
-- url     : https://prove2.me/theorems/07d51990-53d8-4df3-a5f1-a5a2c2fb6887
-- title:
--   `BookProof.ChapterAttentionStreaming.sum_scoreSoftmax_snoc_castSucc` (beta sn : ℝ) (s : Fin m → ℝ) (i : Fin m) : ∑ j : Fin m, scoreSoftmax beta (Fin.snoc s sn) j.castSucc = 1 - new
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionStreaming`.
--
--   `BookProof.ChapterAttentionStreaming.sum_scoreSoftmax_snoc_castSucc` (beta sn : ℝ) (s : Fin m → ℝ) (i : Fin m) : ∑ j : Fin m, scoreSoftmax beta (Fin.snoc s sn) j.castSucc = 1 - newWeight beta sn s
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionStreaming.sum_scoreSoftmax_snoc_castSucc`.

-- Generated from ChapterAttentionStreaming.lean — theorem BookProof.ChapterAttentionStreaming.sum_scoreSoftmax_snoc_castSucc
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionStreaming
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionStreaming


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionStreaming.sum_scoreSoftmax_snoc_castSucc (beta sn : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    ∑ j : Fin m, scoreSoftmax beta (Fin.snoc s sn) j.castSucc = 1 - newWeight beta sn s := by sorry
