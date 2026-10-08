-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionOutput_norm_headOutput_le
-- name    : BookProof.ChapterAttentionOutput.norm_headOutput_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:33:15.935556+00:00
-- url     : https://prove2.me/theorems/de09649c-f085-4771-9026-d5081344cbb5
-- title:
--   `BookProof.ChapterAttentionOutput.norm_headOutput_le` (beta : ℝ) (s : Fin m → ℝ) {v : Fin m → E} {C : ℝ} (hv : ∀ j, ‖v j‖ ≤ C) (i : Fin m) : ‖headOutput beta s v‖ ≤ C
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionOutput`.
--
--   `BookProof.ChapterAttentionOutput.norm_headOutput_le` (beta : ℝ) (s : Fin m → ℝ) {v : Fin m → E} {C : ℝ} (hv : ∀ j, ‖v j‖ ≤ C) (i : Fin m) : ‖headOutput beta s v‖ ≤ C
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionOutput.norm_headOutput_le`.

-- Generated from ChapterAttentionOutput.lean — theorem BookProof.ChapterAttentionOutput.norm_headOutput_le
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionOutput
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionOutput


open scoped BigOperators

open Filter Topology

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionOutput.norm_headOutput_le (beta : ℝ) (s : Fin m → ℝ) {v : Fin m → E} {C : ℝ}
    (hv : ∀ j, ‖v j‖ ≤ C) (i : Fin m) : ‖headOutput beta s v‖ ≤ C := by sorry
