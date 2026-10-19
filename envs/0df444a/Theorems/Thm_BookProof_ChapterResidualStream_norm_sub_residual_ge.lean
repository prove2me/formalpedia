-- Prove2me | Theorems.Thm_BookProof_ChapterResidualStream_norm_sub_residual_ge
-- name    : BookProof.ChapterResidualStream.norm_sub_residual_ge
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T22:59:59.334984+00:00
-- url     : https://prove2.me/theorems/c260b5b1-11f4-458d-805b-0c43f46c9b92
-- title:
--   `BookProof.ChapterResidualStream.norm_sub_residual_ge` {f : E → E} {L : ℝ} (hf : ∀ x y, ‖f x - f y‖ ≤ L * ‖x - y‖) (x y : E) : (1 - L) * ‖x - y‖ ≤ ‖residual f x - residual...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterResidualStream`.
--
--   `BookProof.ChapterResidualStream.norm_sub_residual_ge` {f : E → E} {L : ℝ} (hf : ∀ x y, ‖f x - f y‖ ≤ L * ‖x - y‖) (x y : E) : (1 - L) * ‖x - y‖ ≤ ‖residual f x - residual f y‖
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterResidualStream.norm_sub_residual_ge`.

-- Generated from ChapterResidualStream.lean — theorem BookProof.ChapterResidualStream.norm_sub_residual_ge
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterAttentionOutput
import Mathlib
import Definitions.Def_ChapterResidualStream
open BookProof.ChapterResidualStream


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterAttentionOutput

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E]

theorem BookProof.ChapterResidualStream.norm_sub_residual_ge {f : E → E} {L : ℝ}
    (hf : ∀ x y, ‖f x - f y‖ ≤ L * ‖x - y‖) (x y : E) :
    (1 - L) * ‖x - y‖ ≤ ‖residual f x - residual f y‖ := by sorry
