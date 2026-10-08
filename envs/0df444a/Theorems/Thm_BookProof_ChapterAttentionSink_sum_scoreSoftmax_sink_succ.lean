-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionSink_sum_scoreSoftmax_sink_succ
-- name    : BookProof.ChapterAttentionSink.sum_scoreSoftmax_sink_succ
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:45:57.99459+00:00
-- url     : https://prove2.me/theorems/b65f6810-52ba-41d5-b52d-848b5bc81669
-- title:
--   `BookProof.ChapterAttentionSink.sum_scoreSoftmax_sink_succ` (beta s0 : ℝ) (s : Fin m → ℝ) (i : Fin m) : ∑ j : Fin m, scoreSoftmax beta (Fin.cons s0 s) j.succ = 1 - sinkWeight beta
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionSink`.
--
--   `BookProof.ChapterAttentionSink.sum_scoreSoftmax_sink_succ` (beta s0 : ℝ) (s : Fin m → ℝ) (i : Fin m) : ∑ j : Fin m, scoreSoftmax beta (Fin.cons s0 s) j.succ = 1 - sinkWeight beta s0 s
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionSink.sum_scoreSoftmax_sink_succ`.

-- Generated from ChapterAttentionSink.lean — theorem BookProof.ChapterAttentionSink.sum_scoreSoftmax_sink_succ
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

theorem BookProof.ChapterAttentionSink.sum_scoreSoftmax_sink_succ (beta s0 : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    ∑ j : Fin m, scoreSoftmax beta (Fin.cons s0 s) j.succ = 1 - sinkWeight beta s0 s := by sorry
