-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionStreaming_scoreSoftmax_snoc_castSucc
-- name    : BookProof.ChapterAttentionStreaming.scoreSoftmax_snoc_castSucc
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:50:49.982988+00:00
-- url     : https://prove2.me/theorems/5f05db84-84cf-4219-a2f9-f6d43a2a59b0
-- title:
--   `BookProof.ChapterAttentionStreaming.scoreSoftmax_snoc_castSucc` (beta sn : ℝ) (s : Fin m → ℝ) (j : Fin m) : scoreSoftmax beta (Fin.snoc s sn) j.castSucc = (1 - newWeight beta sn s
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionStreaming`.
--
--   `BookProof.ChapterAttentionStreaming.scoreSoftmax_snoc_castSucc` (beta sn : ℝ) (s : Fin m → ℝ) (j : Fin m) : scoreSoftmax beta (Fin.snoc s sn) j.castSucc = (1 - newWeight beta sn s) * scoreSoftmax beta s j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionStreaming.scoreSoftmax_snoc_castSucc`.

-- Generated from ChapterAttentionStreaming.lean — theorem BookProof.ChapterAttentionStreaming.scoreSoftmax_snoc_castSucc
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

theorem BookProof.ChapterAttentionStreaming.scoreSoftmax_snoc_castSucc (beta sn : ℝ) (s : Fin m → ℝ) (j : Fin m) :
    scoreSoftmax beta (Fin.snoc s sn) j.castSucc
      = (1 - newWeight beta sn s) * scoreSoftmax beta s j := by sorry
