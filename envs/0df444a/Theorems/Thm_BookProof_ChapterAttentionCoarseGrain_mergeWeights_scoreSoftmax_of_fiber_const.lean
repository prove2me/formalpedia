-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionCoarseGrain_mergeWeights_scoreSoftmax_of_fiber_const
-- name    : BookProof.ChapterAttentionCoarseGrain.mergeWeights_scoreSoftmax_of_fiber_const
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:55:00.462347+00:00
-- url     : https://prove2.me/theorems/4dbb8412-88c9-44cf-b2ac-744814d418a3
-- title:
--   `BookProof.ChapterAttentionCoarseGrain.mergeWeights_scoreSoftmax_of_fiber_const` (beta : ℝ) (f : Fin m → Fin r) (t : Fin r → ℝ) (y : Fin r) : mergeWeights f (scoreSoftmax beta (fun
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionCoarseGrain`.
--
--   `BookProof.ChapterAttentionCoarseGrain.mergeWeights_scoreSoftmax_of_fiber_const` (beta : ℝ) (f : Fin m → Fin r) (t : Fin r → ℝ) (y : Fin r) : mergeWeights f (scoreSoftmax beta (fun x => t (f x))) y = ((Finset.univ.filter (fun x => f x = y)).card : ℝ) * Real.exp (beta * t y) / ∑ z, ((Finset.univ.filter (fun x => f x = z)).card : ℝ) * Real.exp (beta * t z)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionCoarseGrain.mergeWeights_scoreSoftmax_of_fiber_const`.

-- Generated from ChapterAttentionCoarseGrain.lean — theorem BookProof.ChapterAttentionCoarseGrain.mergeWeights_scoreSoftmax_of_fiber_const
import Definitions.Def_ChapterObservableExpectation
import Mathlib
import Definitions.Def_ChapterAttentionCoarseGrain
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionCoarseGrain


open scoped BigOperators

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness

variable {m r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionCoarseGrain.mergeWeights_scoreSoftmax_of_fiber_const (beta : ℝ) (f : Fin m → Fin r)
    (t : Fin r → ℝ) (y : Fin r) :
    mergeWeights f (scoreSoftmax beta (fun x => t (f x))) y
      = ((Finset.univ.filter (fun x => f x = y)).card : ℝ) * Real.exp (beta * t y)
        / ∑ z, ((Finset.univ.filter (fun x => f x = z)).card : ℝ) * Real.exp (beta * t z) := by sorry
