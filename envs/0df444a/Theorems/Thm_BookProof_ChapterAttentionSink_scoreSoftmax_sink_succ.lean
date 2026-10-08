-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionSink_scoreSoftmax_sink_succ
-- name    : BookProof.ChapterAttentionSink.scoreSoftmax_sink_succ
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:45:28.499557+00:00
-- url     : https://prove2.me/theorems/c2c6f57e-887e-4db1-807d-49ad5b0f34c9
-- title:
--   `BookProof.ChapterAttentionSink.scoreSoftmax_sink_succ` (beta s0 : ℝ) (s : Fin m → ℝ) (j : Fin m) : scoreSoftmax beta (Fin.cons s0 s) j.succ = (1 - sinkWeight beta s0 s) * scoreSof
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionSink`.
--
--   `BookProof.ChapterAttentionSink.scoreSoftmax_sink_succ` (beta s0 : ℝ) (s : Fin m → ℝ) (j : Fin m) : scoreSoftmax beta (Fin.cons s0 s) j.succ = (1 - sinkWeight beta s0 s) * scoreSoftmax beta s j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionSink.scoreSoftmax_sink_succ`.

-- Generated from ChapterAttentionSink.lean — theorem BookProof.ChapterAttentionSink.scoreSoftmax_sink_succ
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

theorem BookProof.ChapterAttentionSink.scoreSoftmax_sink_succ (beta s0 : ℝ) (s : Fin m → ℝ) (j : Fin m) :
    scoreSoftmax beta (Fin.cons s0 s) j.succ
      = (1 - sinkWeight beta s0 s) * scoreSoftmax beta s j := by sorry
