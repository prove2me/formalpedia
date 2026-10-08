-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionStreaming_scoreSoftmax_snoc_odds
-- name    : BookProof.ChapterAttentionStreaming.scoreSoftmax_snoc_odds
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:50:39.009687+00:00
-- url     : https://prove2.me/theorems/de0f6a89-a372-4265-82c1-9d6b564753a5
-- title:
--   `BookProof.ChapterAttentionStreaming.scoreSoftmax_snoc_odds` (beta sn : ℝ) (s : Fin m → ℝ) (i j : Fin m) : scoreSoftmax beta (Fin.snoc s sn) i.castSucc * scoreSoftmax beta s j = sc
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionStreaming`.
--
--   `BookProof.ChapterAttentionStreaming.scoreSoftmax_snoc_odds` (beta sn : ℝ) (s : Fin m → ℝ) (i j : Fin m) : scoreSoftmax beta (Fin.snoc s sn) i.castSucc * scoreSoftmax beta s j = scoreSoftmax beta (Fin.snoc s sn) j.castSucc * scoreSoftmax beta s i
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionStreaming.scoreSoftmax_snoc_odds`.

-- Generated from ChapterAttentionStreaming.lean — theorem BookProof.ChapterAttentionStreaming.scoreSoftmax_snoc_odds
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

theorem BookProof.ChapterAttentionStreaming.scoreSoftmax_snoc_odds (beta sn : ℝ) (s : Fin m → ℝ) (i j : Fin m) :
    scoreSoftmax beta (Fin.snoc s sn) i.castSucc * scoreSoftmax beta s j
      = scoreSoftmax beta (Fin.snoc s sn) j.castSucc * scoreSoftmax beta s i := by sorry
