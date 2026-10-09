-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionSink_scoreSoftmax_sink_odds
-- name    : BookProof.ChapterAttentionSink.scoreSoftmax_sink_odds
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:45:37.689465+00:00
-- url     : https://prove2.me/theorems/5f62983f-b4c8-423c-9105-bd94d21ba707
-- title:
--   `BookProof.ChapterAttentionSink.scoreSoftmax_sink_odds` (beta s0 : ℝ) (s : Fin m → ℝ) (i j : Fin m) : scoreSoftmax beta (Fin.cons s0 s) i.succ * scoreSoftmax beta s j = scoreSoftma
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionSink`.
--
--   `BookProof.ChapterAttentionSink.scoreSoftmax_sink_odds` (beta s0 : ℝ) (s : Fin m → ℝ) (i j : Fin m) : scoreSoftmax beta (Fin.cons s0 s) i.succ * scoreSoftmax beta s j = scoreSoftmax beta (Fin.cons s0 s) j.succ * scoreSoftmax beta s i
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionSink.scoreSoftmax_sink_odds`.

-- Generated from ChapterAttentionSink.lean — theorem BookProof.ChapterAttentionSink.scoreSoftmax_sink_odds
import Definitions.Def_ChapterObservableExpectation
import Mathlib
import Definitions.Def_ChapterAttentionSink
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionSink


open scoped BigOperators

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionSink.scoreSoftmax_sink_odds (beta s0 : ℝ) (s : Fin m → ℝ) (i j : Fin m) :
    scoreSoftmax beta (Fin.cons s0 s) i.succ * scoreSoftmax beta s j
      = scoreSoftmax beta (Fin.cons s0 s) j.succ * scoreSoftmax beta s i := by sorry
