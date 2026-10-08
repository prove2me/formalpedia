-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionCollision_effectiveSupport_scoreSoftmax_mem_Icc
-- name    : BookProof.ChapterAttentionCollision.effectiveSupport_scoreSoftmax_mem_Icc
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:23:52.697739+00:00
-- url     : https://prove2.me/theorems/e336b329-e21d-46de-953c-8939b7a53457
-- title:
--   `BookProof.ChapterAttentionCollision.effectiveSupport_scoreSoftmax_mem_Icc` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : effectiveSupport (scoreSoftmax beta s) ∈ Set.Icc (1 : ℝ) (m : ℝ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionCollision`.
--
--   `BookProof.ChapterAttentionCollision.effectiveSupport_scoreSoftmax_mem_Icc` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : effectiveSupport (scoreSoftmax beta s) ∈ Set.Icc (1 : ℝ) (m : ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionCollision.effectiveSupport_scoreSoftmax_mem_Icc`.

-- Generated from ChapterAttentionCollision.lean — theorem BookProof.ChapterAttentionCollision.effectiveSupport_scoreSoftmax_mem_Icc
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionCollision
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionCollision


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterAttentionCollision.effectiveSupport_scoreSoftmax_mem_Icc (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    effectiveSupport (scoreSoftmax beta s) ∈ Set.Icc (1 : ℝ) (m : ℝ) := by sorry
