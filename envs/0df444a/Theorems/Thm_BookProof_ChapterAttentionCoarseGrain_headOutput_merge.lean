-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionCoarseGrain_headOutput_merge
-- name    : BookProof.ChapterAttentionCoarseGrain.headOutput_merge
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:22:20.461991+00:00
-- url     : https://prove2.me/theorems/cf6b2239-3077-4431-9d78-53b8afea1e40
-- title:
--   `BookProof.ChapterAttentionCoarseGrain.headOutput_merge` (beta : ℝ) (s : Fin m → ℝ) (f : Fin m → Fin r) (v : Fin r → E) : observableExpectation (mergeWeights f (scoreSoftmax beta s
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionCoarseGrain`.
--
--   `BookProof.ChapterAttentionCoarseGrain.headOutput_merge` (beta : ℝ) (s : Fin m → ℝ) (f : Fin m → Fin r) (v : Fin r → E) : observableExpectation (mergeWeights f (scoreSoftmax beta s)) v = headOutput beta s (fun x => v (f x))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionCoarseGrain.headOutput_merge`.

-- Generated from ChapterAttentionCoarseGrain.lean — theorem BookProof.ChapterAttentionCoarseGrain.headOutput_merge
import Mathlib
import Definitions.Def_ChapterAttentionCoarseGrain
import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterAttentionOutput
open BookProof.ChapterObservableExpectation
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionCoarseGrain


open scoped BigOperators

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionOutput

variable {m r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionCoarseGrain.headOutput_merge (beta : ℝ) (s : Fin m → ℝ) (f : Fin m → Fin r) (v : Fin r → E) :
    observableExpectation (mergeWeights f (scoreSoftmax beta s)) v
      = headOutput beta s (fun x => v (f x)) := by sorry
