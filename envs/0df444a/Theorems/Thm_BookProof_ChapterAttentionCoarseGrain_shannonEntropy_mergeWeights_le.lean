-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionCoarseGrain_shannonEntropy_mergeWeights_le
-- name    : BookProof.ChapterAttentionCoarseGrain.shannonEntropy_mergeWeights_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:20:39.338978+00:00
-- url     : https://prove2.me/theorems/15f51842-fcf4-4677-aabd-6fb21f75e812
-- title:
--   `BookProof.ChapterAttentionCoarseGrain.shannonEntropy_mergeWeights_le` {f : Fin m → Fin r} {p : Fin m → ℝ} (hp : ∀ x, 0 ≤ p x) : shannonEntropy (mergeWeights f p) ≤ shannonEntropy
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionCoarseGrain`.
--
--   `BookProof.ChapterAttentionCoarseGrain.shannonEntropy_mergeWeights_le` {f : Fin m → Fin r} {p : Fin m → ℝ} (hp : ∀ x, 0 ≤ p x) : shannonEntropy (mergeWeights f p) ≤ shannonEntropy p
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionCoarseGrain.shannonEntropy_mergeWeights_le`.

-- Generated from ChapterAttentionCoarseGrain.lean — theorem BookProof.ChapterAttentionCoarseGrain.shannonEntropy_mergeWeights_le
import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterAttentionCoarseGrain
import Definitions.Def_ChapterAttentionEntropy
open BookProof.ChapterAttentionCoarseGrain


open scoped BigOperators

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionEntropy

variable {m r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionCoarseGrain.shannonEntropy_mergeWeights_le {f : Fin m → Fin r} {p : Fin m → ℝ}
    (hp : ∀ x, 0 ≤ p x) :
    shannonEntropy (mergeWeights f p) ≤ shannonEntropy p := by sorry
