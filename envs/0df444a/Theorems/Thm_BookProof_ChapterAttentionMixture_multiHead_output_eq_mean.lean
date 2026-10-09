-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionMixture_multiHead_output_eq_mean
-- name    : BookProof.ChapterAttentionMixture.multiHead_output_eq_mean
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:31:57.593832+00:00
-- url     : https://prove2.me/theorems/746115a5-309c-4d6f-b82c-b16ae0b8a253
-- title:
--   `BookProof.ChapterAttentionMixture.multiHead_output_eq_mean` (w : Fin H → ℝ) (beta : Fin H → ℝ) (s : Fin H → Fin m → ℝ) (v : Fin m → E) : observableExpectation (multiHead w beta s)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionMixture`.
--
--   `BookProof.ChapterAttentionMixture.multiHead_output_eq_mean` (w : Fin H → ℝ) (beta : Fin H → ℝ) (s : Fin H → Fin m → ℝ) (v : Fin m → E) : observableExpectation (multiHead w beta s) v = ∑ h, w h • headOutput (beta h) (s h) v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionMixture.multiHead_output_eq_mean`.

-- Generated from ChapterAttentionMixture.lean — theorem BookProof.ChapterAttentionMixture.multiHead_output_eq_mean
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionMixture
import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterAttentionOutput
open BookProof.ChapterObservableExpectation
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionMixture


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterAttentionOutput

variable {m H : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionMixture.multiHead_output_eq_mean (w : Fin H → ℝ) (beta : Fin H → ℝ)
    (s : Fin H → Fin m → ℝ) (v : Fin m → E) :
    observableExpectation (multiHead w beta s) v
      = ∑ h, w h • headOutput (beta h) (s h) v := by sorry
