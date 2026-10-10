-- Prove2me | Theorems.Thm_BookProof_ChapterResidualStream_norm_iterate_residual_sub_le
-- name    : BookProof.ChapterResidualStream.norm_iterate_residual_sub_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:03:55.509572+00:00
-- url     : https://prove2.me/theorems/bc9f58d1-449c-4990-9f0e-2df32ae59887
-- title:
--   `BookProof.ChapterResidualStream.norm_iterate_residual_sub_le` {f : E → E} {C : ℝ} (hf : ∀ x, ‖f x‖ ≤ C) (n : ℕ) (x : E) : ‖(residual f)^[n] x - x‖ ≤ n * C
-- statement:
--   Prove the following Lean 4 theorem from `ChapterResidualStream`.
--
--   `BookProof.ChapterResidualStream.norm_iterate_residual_sub_le` {f : E → E} {C : ℝ} (hf : ∀ x, ‖f x‖ ≤ C) (n : ℕ) (x : E) : ‖(residual f)^[n] x - x‖ ≤ n * C
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterResidualStream.norm_iterate_residual_sub_le`.

-- Generated from ChapterResidualStream.lean — theorem BookProof.ChapterResidualStream.norm_iterate_residual_sub_le
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterAttentionOutput
import Mathlib
import Definitions.Def_ChapterResidualStream
open BookProof.ChapterResidualStream


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterAttentionOutput

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E]

theorem BookProof.ChapterResidualStream.norm_iterate_residual_sub_le {f : E → E} {C : ℝ} (hf : ∀ x, ‖f x‖ ≤ C) (n : ℕ)
    (x : E) :
    ‖(residual f)^[n] x - x‖ ≤ n * C := by sorry
