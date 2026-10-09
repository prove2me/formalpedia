-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionSink_one_sub_sinkWeight_eq
-- name    : BookProof.ChapterAttentionSink.one_sub_sinkWeight_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:45:31.757197+00:00
-- url     : https://prove2.me/theorems/a46061fb-0f5c-4b72-a921-b351f1f1552e
-- title:
--   `BookProof.ChapterAttentionSink.one_sub_sinkWeight_eq` (beta s0 : ℝ) (s : Fin m → ℝ) : 1 - sinkWeight beta s0 s = (∑ l, Real.exp (beta * s l)) / (Real.exp (beta * s0) + ∑ l, Real.e
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionSink`.
--
--   `BookProof.ChapterAttentionSink.one_sub_sinkWeight_eq` (beta s0 : ℝ) (s : Fin m → ℝ) : 1 - sinkWeight beta s0 s = (∑ l, Real.exp (beta * s l)) / (Real.exp (beta * s0) + ∑ l, Real.exp (beta * s l))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionSink.one_sub_sinkWeight_eq`.

-- Generated from ChapterAttentionSink.lean — theorem BookProof.ChapterAttentionSink.one_sub_sinkWeight_eq
import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterAttentionSink
open BookProof.ChapterAttentionSink


open scoped BigOperators

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionSink.one_sub_sinkWeight_eq (beta s0 : ℝ) (s : Fin m → ℝ) :
    1 - sinkWeight beta s0 s
      = (∑ l, Real.exp (beta * s l)) / (Real.exp (beta * s0) + ∑ l, Real.exp (beta * s l)) := by sorry
