-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionStreaming_one_sub_newWeight_eq
-- name    : BookProof.ChapterAttentionStreaming.one_sub_newWeight_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:50:40.811548+00:00
-- url     : https://prove2.me/theorems/d6f75bb9-83de-4ad9-9ddb-94341f0f30bb
-- title:
--   `BookProof.ChapterAttentionStreaming.one_sub_newWeight_eq` (beta sn : ℝ) (s : Fin m → ℝ) : 1 - newWeight beta sn s = (∑ l, Real.exp (beta * s l)) / ((∑ l, Real.exp (beta * s l)) +
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionStreaming`.
--
--   `BookProof.ChapterAttentionStreaming.one_sub_newWeight_eq` (beta sn : ℝ) (s : Fin m → ℝ) : 1 - newWeight beta sn s = (∑ l, Real.exp (beta * s l)) / ((∑ l, Real.exp (beta * s l)) + Real.exp (beta * sn))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionStreaming.one_sub_newWeight_eq`.

-- Generated from ChapterAttentionStreaming.lean — theorem BookProof.ChapterAttentionStreaming.one_sub_newWeight_eq
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionStreaming
open BookProof.ChapterAttentionStreaming


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionStreaming.one_sub_newWeight_eq (beta sn : ℝ) (s : Fin m → ℝ) :
    1 - newWeight beta sn s
      = (∑ l, Real.exp (beta * s l))
          / ((∑ l, Real.exp (beta * s l)) + Real.exp (beta * sn)) := by sorry
