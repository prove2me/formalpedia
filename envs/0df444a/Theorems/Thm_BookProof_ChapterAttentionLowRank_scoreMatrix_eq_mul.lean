-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionLowRank_scoreMatrix_eq_mul
-- name    : BookProof.ChapterAttentionLowRank.scoreMatrix_eq_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:28:29.753673+00:00
-- url     : https://prove2.me/theorems/e1c0b9f4-7dce-4355-8479-d7aa6a335b2e
-- title:
--   `BookProof.ChapterAttentionLowRank.scoreMatrix_eq_mul` (Q K : Fin m → Fin d → ℝ) : scoreMatrix Q K = (Matrix.of Q) * (Matrix.of K).transpose
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionLowRank`.
--
--   `BookProof.ChapterAttentionLowRank.scoreMatrix_eq_mul` (Q K : Fin m → Fin d → ℝ) : scoreMatrix Q K = (Matrix.of Q) * (Matrix.of K).transpose
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionLowRank.scoreMatrix_eq_mul`.

-- Generated from ChapterAttentionLowRank.lean — theorem BookProof.ChapterAttentionLowRank.scoreMatrix_eq_mul
import Mathlib
import Definitions.Def_ChapterAttentionLowRank
open BookProof.ChapterAttentionLowRank


open scoped BigOperators

noncomputable section


variable {m d : ℕ}

theorem BookProof.ChapterAttentionLowRank.scoreMatrix_eq_mul (Q K : Fin m → Fin d → ℝ) :
    scoreMatrix Q K = (Matrix.of Q) * (Matrix.of K).transpose := by sorry
