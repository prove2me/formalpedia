-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionSink_sink_denom
-- name    : BookProof.ChapterAttentionSink.sink_denom
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:44:21.957221+00:00
-- url     : https://prove2.me/theorems/6c20e9a8-d230-41f8-ac44-75e77eab4fc6
-- title:
--   `BookProof.ChapterAttentionSink.sink_denom` (beta s0 : ℝ) (s : Fin m → ℝ) : ∑ l, Real.exp (beta * (Fin.cons s0 s : Fin (m + 1) → ℝ) l) = Real.exp (beta * s0) + ∑ l, Real.exp (beta
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionSink`.
--
--   `BookProof.ChapterAttentionSink.sink_denom` (beta s0 : ℝ) (s : Fin m → ℝ) : ∑ l, Real.exp (beta * (Fin.cons s0 s : Fin (m + 1) → ℝ) l) = Real.exp (beta * s0) + ∑ l, Real.exp (beta * s l)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionSink.sink_denom`.

-- Generated from ChapterAttentionSink.lean — theorem BookProof.ChapterAttentionSink.sink_denom
import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterAttentionSink
open BookProof.ChapterAttentionSink


open scoped BigOperators

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionSink.sink_denom (beta s0 : ℝ) (s : Fin m → ℝ) :
    ∑ l, Real.exp (beta * (Fin.cons s0 s : Fin (m + 1) → ℝ) l)
      = Real.exp (beta * s0) + ∑ l, Real.exp (beta * s l) := by sorry
