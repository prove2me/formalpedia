-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionSink_sink_denom_pos
-- name    : BookProof.ChapterAttentionSink.sink_denom_pos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:44:38.233981+00:00
-- url     : https://prove2.me/theorems/35e23ae3-a1b1-40e4-a74e-36127b69331a
-- title:
--   `BookProof.ChapterAttentionSink.sink_denom_pos` (beta s0 : ℝ) (s : Fin m → ℝ) : 0 < Real.exp (beta * s0) + ∑ l, Real.exp (beta * s l)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionSink`.
--
--   `BookProof.ChapterAttentionSink.sink_denom_pos` (beta s0 : ℝ) (s : Fin m → ℝ) : 0 < Real.exp (beta * s0) + ∑ l, Real.exp (beta * s l)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionSink.sink_denom_pos`.

-- Generated from ChapterAttentionSink.lean — theorem BookProof.ChapterAttentionSink.sink_denom_pos
import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterAttentionSink
open BookProof.ChapterAttentionSink


open scoped BigOperators

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionSink.sink_denom_pos (beta s0 : ℝ) (s : Fin m → ℝ) :
    0 < Real.exp (beta * s0) + ∑ l, Real.exp (beta * s l) := by sorry
