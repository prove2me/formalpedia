-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionStreaming_norm_headOutput_snoc_sub_le
-- name    : BookProof.ChapterAttentionStreaming.norm_headOutput_snoc_sub_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:29:48.225154+00:00
-- url     : https://prove2.me/theorems/33bbd2fb-80c1-4015-9028-8168448df161
-- title:
--   `BookProof.ChapterAttentionStreaming.norm_headOutput_snoc_sub_le` (beta sn : ℝ) (s : Fin m → ℝ) (vn : E) (v : Fin m → E) : ‖headOutput beta (Fin.snoc s sn) (Fin.snoc v vn) - headOu
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionStreaming`.
--
--   `BookProof.ChapterAttentionStreaming.norm_headOutput_snoc_sub_le` (beta sn : ℝ) (s : Fin m → ℝ) (vn : E) (v : Fin m → E) : ‖headOutput beta (Fin.snoc s sn) (Fin.snoc v vn) - headOutput beta s v‖ = newWeight beta sn s * ‖vn - headOutput beta s v‖
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionStreaming.norm_headOutput_snoc_sub_le`.

-- Generated from ChapterAttentionStreaming.lean — theorem BookProof.ChapterAttentionStreaming.norm_headOutput_snoc_sub_le
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionStreaming
import Definitions.Def_ChapterAttentionOutput
open BookProof.ChapterAttentionStreaming


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterAttentionOutput

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionStreaming.norm_headOutput_snoc_sub_le (beta sn : ℝ) (s : Fin m → ℝ) (vn : E) (v : Fin m → E) :
    ‖headOutput beta (Fin.snoc s sn) (Fin.snoc v vn) - headOutput beta s v‖
      = newWeight beta sn s * ‖vn - headOutput beta s v‖ := by sorry
