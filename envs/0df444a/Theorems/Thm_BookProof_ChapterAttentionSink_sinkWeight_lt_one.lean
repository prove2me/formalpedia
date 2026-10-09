-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionSink_sinkWeight_lt_one
-- name    : BookProof.ChapterAttentionSink.sinkWeight_lt_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:45:37.077471+00:00
-- url     : https://prove2.me/theorems/53145ce9-13a4-4293-a751-4d54fda5bd4d
-- title:
--   `BookProof.ChapterAttentionSink.sinkWeight_lt_one` (beta s0 : ℝ) (s : Fin m → ℝ) (i : Fin m) : sinkWeight beta s0 s < 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionSink`.
--
--   `BookProof.ChapterAttentionSink.sinkWeight_lt_one` (beta s0 : ℝ) (s : Fin m → ℝ) (i : Fin m) : sinkWeight beta s0 s < 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionSink.sinkWeight_lt_one`.

-- Generated from ChapterAttentionSink.lean — theorem BookProof.ChapterAttentionSink.sinkWeight_lt_one
import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterAttentionSink
open BookProof.ChapterAttentionSink


open scoped BigOperators

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionSink.sinkWeight_lt_one (beta s0 : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    sinkWeight beta s0 s < 1 := by sorry
