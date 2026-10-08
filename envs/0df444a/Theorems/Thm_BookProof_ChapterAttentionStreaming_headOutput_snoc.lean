-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionStreaming_headOutput_snoc
-- name    : BookProof.ChapterAttentionStreaming.headOutput_snoc
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:51:38.743908+00:00
-- url     : https://prove2.me/theorems/ba02611e-5093-452b-a968-9d0ae31b63c4
-- title:
--   `BookProof.ChapterAttentionStreaming.headOutput_snoc` (beta sn : ℝ) (s : Fin m → ℝ) (vn : E) (v : Fin m → E) : headOutput beta (Fin.snoc s sn) (Fin.snoc v vn) = (1 - newWeight beta
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionStreaming`.
--
--   `BookProof.ChapterAttentionStreaming.headOutput_snoc` (beta sn : ℝ) (s : Fin m → ℝ) (vn : E) (v : Fin m → E) : headOutput beta (Fin.snoc s sn) (Fin.snoc v vn) = (1 - newWeight beta sn s) • headOutput beta s v + newWeight beta sn s • vn
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionStreaming.headOutput_snoc`.

-- Generated from ChapterAttentionStreaming.lean — theorem BookProof.ChapterAttentionStreaming.headOutput_snoc
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionStreaming
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterAttentionOutput
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionStreaming


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterAttentionOutput

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionStreaming.headOutput_snoc (beta sn : ℝ) (s : Fin m → ℝ) (vn : E) (v : Fin m → E) :
    headOutput beta (Fin.snoc s sn) (Fin.snoc v vn)
      = (1 - newWeight beta sn s) • headOutput beta s v + newWeight beta sn s • vn := by sorry
