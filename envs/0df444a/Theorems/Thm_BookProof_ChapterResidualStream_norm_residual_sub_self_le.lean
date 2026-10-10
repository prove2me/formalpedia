-- Prove2me | Theorems.Thm_BookProof_ChapterResidualStream_norm_residual_sub_self_le
-- name    : BookProof.ChapterResidualStream.norm_residual_sub_self_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:03:48.921835+00:00
-- url     : https://prove2.me/theorems/9db68db1-ea36-450d-b08a-19deab5b5e5b
-- title:
--   `BookProof.ChapterResidualStream.norm_residual_sub_self_le` [NormedSpace ℝ E] (beta : ℝ) (s : Fin m → ℝ) {v : Fin m → E} {C : ℝ} (hv : ∀ j, ‖v j‖ ≤ C) (i : Fin m) (x : E) :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterResidualStream`.
--
--   `BookProof.ChapterResidualStream.norm_residual_sub_self_le` [NormedSpace ℝ E] (beta : ℝ) (s : Fin m → ℝ) {v : Fin m → E} {C : ℝ} (hv : ∀ j, ‖v j‖ ≤ C) (i : Fin m) (x : E) : ‖residual (fun _ => headOutput beta s v) x - x‖ ≤ C
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterResidualStream.norm_residual_sub_self_le`.

-- Generated from ChapterResidualStream.lean — theorem BookProof.ChapterResidualStream.norm_residual_sub_self_le
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterAttentionOutput
import Mathlib
import Definitions.Def_ChapterResidualStream
open BookProof.ChapterResidualStream


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterAttentionOutput

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E]

theorem BookProof.ChapterResidualStream.norm_residual_sub_self_le [NormedSpace ℝ E] (beta : ℝ) (s : Fin m → ℝ)
    {v : Fin m → E} {C : ℝ} (hv : ∀ j, ‖v j‖ ≤ C) (i : Fin m) (x : E) :
    ‖residual (fun _ => headOutput beta s v) x - x‖ ≤ C := by sorry
