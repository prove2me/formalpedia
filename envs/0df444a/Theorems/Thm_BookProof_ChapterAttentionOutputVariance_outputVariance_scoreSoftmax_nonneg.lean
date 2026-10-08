-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionOutputVariance_outputVariance_scoreSoftmax_nonneg
-- name    : BookProof.ChapterAttentionOutputVariance.outputVariance_scoreSoftmax_nonneg
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:38:23.591321+00:00
-- url     : https://prove2.me/theorems/e84a42ec-c079-4d46-996a-2e7cb5d7d9eb
-- title:
--   `BookProof.ChapterAttentionOutputVariance.outputVariance_scoreSoftmax_nonneg` (beta : ℝ) (s : Fin m → ℝ) (v : Fin m → E) : 0 ≤ outputVariance (scoreSoftmax beta s) v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionOutputVariance`.
--
--   `BookProof.ChapterAttentionOutputVariance.outputVariance_scoreSoftmax_nonneg` (beta : ℝ) (s : Fin m → ℝ) (v : Fin m → E) : 0 ≤ outputVariance (scoreSoftmax beta s) v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionOutputVariance.outputVariance_scoreSoftmax_nonneg`.

-- Generated from ChapterAttentionOutputVariance.lean — theorem BookProof.ChapterAttentionOutputVariance.outputVariance_scoreSoftmax_nonneg
import Definitions.Def_ChapterObservableExpectation
import Mathlib
import Definitions.Def_ChapterAttentionOutputVariance
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionOutputVariance


open scoped BigOperators RealInnerProductSpace

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem BookProof.ChapterAttentionOutputVariance.outputVariance_scoreSoftmax_nonneg (beta : ℝ) (s : Fin m → ℝ) (v : Fin m → E) :
    0 ≤ outputVariance (scoreSoftmax beta s) v := by sorry
