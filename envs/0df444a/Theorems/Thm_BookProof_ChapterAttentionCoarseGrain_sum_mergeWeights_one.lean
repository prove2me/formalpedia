-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionCoarseGrain_sum_mergeWeights_one
-- name    : BookProof.ChapterAttentionCoarseGrain.sum_mergeWeights_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:54:39.039179+00:00
-- url     : https://prove2.me/theorems/c6584775-c8c4-4357-bf0a-1d56dc701530
-- title:
--   `BookProof.ChapterAttentionCoarseGrain.sum_mergeWeights_one` {f : Fin m → Fin r} {p : Fin m → ℝ} (hp : ∑ x, p x = 1) : ∑ y, mergeWeights f p y = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionCoarseGrain`.
--
--   `BookProof.ChapterAttentionCoarseGrain.sum_mergeWeights_one` {f : Fin m → Fin r} {p : Fin m → ℝ} (hp : ∑ x, p x = 1) : ∑ y, mergeWeights f p y = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionCoarseGrain.sum_mergeWeights_one`.

-- Generated from ChapterAttentionCoarseGrain.lean — theorem BookProof.ChapterAttentionCoarseGrain.sum_mergeWeights_one
import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterAttentionCoarseGrain
open BookProof.ChapterAttentionCoarseGrain


open scoped BigOperators

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness

variable {m r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionCoarseGrain.sum_mergeWeights_one {f : Fin m → Fin r} {p : Fin m → ℝ} (hp : ∑ x, p x = 1) :
    ∑ y, mergeWeights f p y = 1 := by sorry
