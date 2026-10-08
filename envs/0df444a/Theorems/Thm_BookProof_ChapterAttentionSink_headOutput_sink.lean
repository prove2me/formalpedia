-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionSink_headOutput_sink
-- name    : BookProof.ChapterAttentionSink.headOutput_sink
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:48:44.246984+00:00
-- url     : https://prove2.me/theorems/e4c303d6-f264-4971-9ff7-6f1ff92a8b8b
-- title:
--   `BookProof.ChapterAttentionSink.headOutput_sink` (beta s0 : ℝ) (s : Fin m → ℝ) (v0 : E) (v : Fin m → E) : headOutput beta (Fin.cons s0 s) (Fin.cons v0 v) = sinkWeight beta s0 s • v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionSink`.
--
--   `BookProof.ChapterAttentionSink.headOutput_sink` (beta s0 : ℝ) (s : Fin m → ℝ) (v0 : E) (v : Fin m → E) : headOutput beta (Fin.cons s0 s) (Fin.cons v0 v) = sinkWeight beta s0 s • v0 + (1 - sinkWeight beta s0 s) • headOutput beta s v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionSink.headOutput_sink`.

-- Generated from ChapterAttentionSink.lean — theorem BookProof.ChapterAttentionSink.headOutput_sink
import Definitions.Def_ChapterObservableExpectation
import Mathlib
import Definitions.Def_ChapterAttentionSink
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterAttentionOutput
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionSink


open scoped BigOperators

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionOutput

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionSink.headOutput_sink (beta s0 : ℝ) (s : Fin m → ℝ) (v0 : E) (v : Fin m → E) :
    headOutput beta (Fin.cons s0 s) (Fin.cons v0 v)
      = sinkWeight beta s0 s • v0 + (1 - sinkWeight beta s0 s) • headOutput beta s v := by sorry
