-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionOutputVariance_outputVariance_scoreSoftmax_eq_zero_iff
-- name    : BookProof.ChapterAttentionOutputVariance.outputVariance_scoreSoftmax_eq_zero_iff
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:38:36.052304+00:00
-- url     : https://prove2.me/theorems/a0274bd7-1f27-4458-b8a3-f492924fe179
-- title:
--   `BookProof.ChapterAttentionOutputVariance.outputVariance_scoreSoftmax_eq_zero_iff` (beta : ℝ) (s : Fin m → ℝ) (v : Fin m → E) : outputVariance (scoreSoftmax beta s) v = 0 ↔ ∀ j, v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionOutputVariance`.
--
--   `BookProof.ChapterAttentionOutputVariance.outputVariance_scoreSoftmax_eq_zero_iff` (beta : ℝ) (s : Fin m → ℝ) (v : Fin m → E) : outputVariance (scoreSoftmax beta s) v = 0 ↔ ∀ j, v j = headOutput beta s v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionOutputVariance.outputVariance_scoreSoftmax_eq_zero_iff`.

-- Generated from ChapterAttentionOutputVariance.lean — theorem BookProof.ChapterAttentionOutputVariance.outputVariance_scoreSoftmax_eq_zero_iff
import Definitions.Def_ChapterObservableExpectation
import Mathlib
import Definitions.Def_ChapterAttentionOutputVariance
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionOutputVariance


open scoped BigOperators RealInnerProductSpace

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionOutput

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem BookProof.ChapterAttentionOutputVariance.outputVariance_scoreSoftmax_eq_zero_iff (beta : ℝ) (s : Fin m → ℝ) (v : Fin m → E) :
    outputVariance (scoreSoftmax beta s) v = 0 ↔ ∀ j, v j = headOutput beta s v := by sorry
