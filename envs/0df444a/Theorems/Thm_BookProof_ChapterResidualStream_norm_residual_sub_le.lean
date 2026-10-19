-- Prove2me | Theorems.Thm_BookProof_ChapterResidualStream_norm_residual_sub_le
-- name    : BookProof.ChapterResidualStream.norm_residual_sub_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:47:27.447268+00:00
-- url     : https://prove2.me/theorems/b9bb835c-18fc-480c-9dd6-edfc02bc4325
-- title:
--   `BookProof.ChapterResidualStream.norm_residual_sub_le` {f : E → E} {L : ℝ} (hf : ∀ x y, ‖f x - f y‖ ≤ L * ‖x - y‖) (x y : E) : ‖residual f x - residual f y‖ ≤ (1 + L) * ‖x...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterResidualStream`.
--
--   `BookProof.ChapterResidualStream.norm_residual_sub_le` {f : E → E} {L : ℝ} (hf : ∀ x y, ‖f x - f y‖ ≤ L * ‖x - y‖) (x y : E) : ‖residual f x - residual f y‖ ≤ (1 + L) * ‖x - y‖
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterResidualStream.norm_residual_sub_le`.

-- Generated from ChapterResidualStream.lean — theorem BookProof.ChapterResidualStream.norm_residual_sub_le
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterAttentionOutput
import Mathlib
import Definitions.Def_ChapterResidualStream
open BookProof.ChapterResidualStream


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterAttentionOutput

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E]

theorem BookProof.ChapterResidualStream.norm_residual_sub_le {f : E → E} {L : ℝ}
    (hf : ∀ x y, ‖f x - f y‖ ≤ L * ‖x - y‖) (x y : E) :
    ‖residual f x - residual f y‖ ≤ (1 + L) * ‖x - y‖ := by sorry
