-- Prove2me | Theorems.Thm_BookProof_ChapterResidualStream_residual_injective
-- name    : BookProof.ChapterResidualStream.residual_injective
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:04:00.960454+00:00
-- url     : https://prove2.me/theorems/3e7d6f01-3e3a-4be5-9b56-2d751cc29a6f
-- title:
--   `BookProof.ChapterResidualStream.residual_injective` {f : E → E} {L : ℝ} (hL : L < 1) (hf : ∀ x y, ‖f x - f y‖ ≤ L * ‖x - y‖) : Function.Injective (residual f)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterResidualStream`.
--
--   `BookProof.ChapterResidualStream.residual_injective` {f : E → E} {L : ℝ} (hL : L < 1) (hf : ∀ x y, ‖f x - f y‖ ≤ L * ‖x - y‖) : Function.Injective (residual f)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterResidualStream.residual_injective`.

-- Generated from ChapterResidualStream.lean — theorem BookProof.ChapterResidualStream.residual_injective
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterAttentionOutput
import Mathlib
import Definitions.Def_ChapterResidualStream
open BookProof.ChapterResidualStream


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterAttentionOutput

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E]

theorem BookProof.ChapterResidualStream.residual_injective {f : E → E} {L : ℝ} (hL : L < 1)
    (hf : ∀ x y, ‖f x - f y‖ ≤ L * ‖x - y‖) :
    Function.Injective (residual f) := by sorry
