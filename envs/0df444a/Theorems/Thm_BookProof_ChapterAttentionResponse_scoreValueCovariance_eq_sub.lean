-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionResponse_scoreValueCovariance_eq_sub
-- name    : BookProof.ChapterAttentionResponse.scoreValueCovariance_eq_sub
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T10:29:13.971322+00:00
-- url     : https://prove2.me/theorems/53f2fd9a-6d05-4410-a151-98e9e75c586d
-- title:
--   `BookProof.ChapterAttentionResponse.scoreValueCovariance_eq_sub` (beta : ℝ) (s : Fin m → ℝ) (v : Fin m → E) : scoreValueCovariance beta s v = (∑ j, (scoreSoftmax beta s j * s j) •
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionResponse`.
--
--   `BookProof.ChapterAttentionResponse.scoreValueCovariance_eq_sub` (beta : ℝ) (s : Fin m → ℝ) (v : Fin m → E) : scoreValueCovariance beta s v = (∑ j, (scoreSoftmax beta s j * s j) • v j) - meanScore beta s • headOutput beta s v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionResponse.scoreValueCovariance_eq_sub`.

-- Generated from ChapterAttentionResponse.lean — theorem BookProof.ChapterAttentionResponse.scoreValueCovariance_eq_sub
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionResponse
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxFluctuation
import Definitions.Def_ChapterAttentionOutput
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionResponse


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterSoftmaxFluctuation
open BookProof.ChapterAttentionOutput

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionResponse.scoreValueCovariance_eq_sub (beta : ℝ) (s : Fin m → ℝ) (v : Fin m → E) :
    scoreValueCovariance beta s v
      = (∑ j, (scoreSoftmax beta s j * s j) • v j) - meanScore beta s • headOutput beta s v := by sorry
