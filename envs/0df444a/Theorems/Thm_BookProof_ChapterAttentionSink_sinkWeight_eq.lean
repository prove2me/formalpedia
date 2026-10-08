-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionSink_sinkWeight_eq
-- name    : BookProof.ChapterAttentionSink.sinkWeight_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:44:31.841263+00:00
-- url     : https://prove2.me/theorems/c0b95e81-2802-446a-b93e-aebd59a3683f
-- title:
--   `BookProof.ChapterAttentionSink.sinkWeight_eq` (beta s0 : ℝ) (s : Fin m → ℝ) : sinkWeight beta s0 s = Real.exp (beta * s0) / (Real.exp (beta * s0) + ∑ l, Real.exp (beta * s l))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionSink`.
--
--   `BookProof.ChapterAttentionSink.sinkWeight_eq` (beta s0 : ℝ) (s : Fin m → ℝ) : sinkWeight beta s0 s = Real.exp (beta * s0) / (Real.exp (beta * s0) + ∑ l, Real.exp (beta * s l))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionSink.sinkWeight_eq`.

-- Generated from ChapterAttentionSink.lean — theorem BookProof.ChapterAttentionSink.sinkWeight_eq
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

theorem BookProof.ChapterAttentionSink.sinkWeight_eq (beta s0 : ℝ) (s : Fin m → ℝ) :
    sinkWeight beta s0 s
      = Real.exp (beta * s0) / (Real.exp (beta * s0) + ∑ l, Real.exp (beta * s l)) := by sorry
