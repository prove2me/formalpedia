-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionStreaming_newWeight_eq
-- name    : BookProof.ChapterAttentionStreaming.newWeight_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:50:22.071984+00:00
-- url     : https://prove2.me/theorems/e7a1001b-3db6-4351-b32d-c22fe05bc9d0
-- title:
--   `BookProof.ChapterAttentionStreaming.newWeight_eq` (beta sn : ℝ) (s : Fin m → ℝ) : newWeight beta sn s = Real.exp (beta * sn) / ((∑ l, Real.exp (beta * s l)) + Real.exp (beta * sn)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionStreaming`.
--
--   `BookProof.ChapterAttentionStreaming.newWeight_eq` (beta sn : ℝ) (s : Fin m → ℝ) : newWeight beta sn s = Real.exp (beta * sn) / ((∑ l, Real.exp (beta * s l)) + Real.exp (beta * sn))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionStreaming.newWeight_eq`.

-- Generated from ChapterAttentionStreaming.lean — theorem BookProof.ChapterAttentionStreaming.newWeight_eq
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionStreaming
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionStreaming


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionStreaming.newWeight_eq (beta sn : ℝ) (s : Fin m → ℝ) :
    newWeight beta sn s
      = Real.exp (beta * sn) / ((∑ l, Real.exp (beta * s l)) + Real.exp (beta * sn)) := by sorry
