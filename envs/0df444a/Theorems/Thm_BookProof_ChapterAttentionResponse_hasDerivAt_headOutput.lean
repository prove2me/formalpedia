-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionResponse_hasDerivAt_headOutput
-- name    : BookProof.ChapterAttentionResponse.hasDerivAt_headOutput
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:42:04.02481+00:00
-- url     : https://prove2.me/theorems/b5c1d615-7b3b-41ea-ae7b-eb90da145470
-- title:
--   `BookProof.ChapterAttentionResponse.hasDerivAt_headOutput` (beta : ℝ) (s : Fin m → ℝ) (v : Fin m → E) : HasDerivAt (fun b : ℝ => headOutput b s v) (scoreValueCovariance beta s v) b
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionResponse`.
--
--   `BookProof.ChapterAttentionResponse.hasDerivAt_headOutput` (beta : ℝ) (s : Fin m → ℝ) (v : Fin m → E) : HasDerivAt (fun b : ℝ => headOutput b s v) (scoreValueCovariance beta s v) beta
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionResponse.hasDerivAt_headOutput`.

-- Generated from ChapterAttentionResponse.lean — theorem BookProof.ChapterAttentionResponse.hasDerivAt_headOutput
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionResponse
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterAttentionOutput
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionResponse


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterAttentionOutput

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionResponse.hasDerivAt_headOutput (beta : ℝ) (s : Fin m → ℝ) (v : Fin m → E) :
    HasDerivAt (fun b : ℝ => headOutput b s v) (scoreValueCovariance beta s v) beta := by sorry
