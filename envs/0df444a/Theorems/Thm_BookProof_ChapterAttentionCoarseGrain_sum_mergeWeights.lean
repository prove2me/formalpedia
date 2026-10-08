-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionCoarseGrain_sum_mergeWeights
-- name    : BookProof.ChapterAttentionCoarseGrain.sum_mergeWeights
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:54:30.572844+00:00
-- url     : https://prove2.me/theorems/5935b443-d58f-4c67-9f39-8b6aee11fce0
-- title:
--   `BookProof.ChapterAttentionCoarseGrain.sum_mergeWeights` (f : Fin m → Fin r) (p : Fin m → ℝ) : ∑ y, mergeWeights f p y = ∑ x, p x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionCoarseGrain`.
--
--   `BookProof.ChapterAttentionCoarseGrain.sum_mergeWeights` (f : Fin m → Fin r) (p : Fin m → ℝ) : ∑ y, mergeWeights f p y = ∑ x, p x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionCoarseGrain.sum_mergeWeights`.

-- Generated from ChapterAttentionCoarseGrain.lean — theorem BookProof.ChapterAttentionCoarseGrain.sum_mergeWeights
import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterAttentionCoarseGrain
open BookProof.ChapterAttentionCoarseGrain


open scoped BigOperators

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness

variable {m r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionCoarseGrain.sum_mergeWeights (f : Fin m → Fin r) (p : Fin m → ℝ) :
    ∑ y, mergeWeights f p y = ∑ x, p x := by sorry
