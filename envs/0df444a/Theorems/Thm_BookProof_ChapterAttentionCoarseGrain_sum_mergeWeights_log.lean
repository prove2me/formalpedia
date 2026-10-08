-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionCoarseGrain_sum_mergeWeights_log
-- name    : BookProof.ChapterAttentionCoarseGrain.sum_mergeWeights_log
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:54:48.180261+00:00
-- url     : https://prove2.me/theorems/bda1677f-3adc-422d-8052-c68c9e044a1b
-- title:
--   `BookProof.ChapterAttentionCoarseGrain.sum_mergeWeights_log` (f : Fin m → Fin r) (p : Fin m → ℝ) : ∑ y, mergeWeights f p y * Real.log (mergeWeights f p y) = ∑ x, p x * Real.log (me
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionCoarseGrain`.
--
--   `BookProof.ChapterAttentionCoarseGrain.sum_mergeWeights_log` (f : Fin m → Fin r) (p : Fin m → ℝ) : ∑ y, mergeWeights f p y * Real.log (mergeWeights f p y) = ∑ x, p x * Real.log (mergeWeights f p (f x))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionCoarseGrain.sum_mergeWeights_log`.

-- Generated from ChapterAttentionCoarseGrain.lean — theorem BookProof.ChapterAttentionCoarseGrain.sum_mergeWeights_log
import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterAttentionCoarseGrain
open BookProof.ChapterAttentionCoarseGrain


open scoped BigOperators

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness

variable {m r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionCoarseGrain.sum_mergeWeights_log (f : Fin m → Fin r) (p : Fin m → ℝ) :
    ∑ y, mergeWeights f p y * Real.log (mergeWeights f p y)
      = ∑ x, p x * Real.log (mergeWeights f p (f x)) := by sorry
