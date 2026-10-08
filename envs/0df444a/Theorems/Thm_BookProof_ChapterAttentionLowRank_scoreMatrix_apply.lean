-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionLowRank_scoreMatrix_apply
-- name    : BookProof.ChapterAttentionLowRank.scoreMatrix_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:26:41.336767+00:00
-- url     : https://prove2.me/theorems/61f6fcc1-9255-4415-829f-e0021be364aa
-- title:
--   `BookProof.ChapterAttentionLowRank.scoreMatrix_apply` (Q K : Fin m → Fin d → ℝ) (i j : Fin m) : scoreMatrix Q K i j = ∑ a, Q i a * K j a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionLowRank`.
--
--   `BookProof.ChapterAttentionLowRank.scoreMatrix_apply` (Q K : Fin m → Fin d → ℝ) (i j : Fin m) : scoreMatrix Q K i j = ∑ a, Q i a * K j a
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionLowRank.scoreMatrix_apply`.

-- Generated from ChapterAttentionLowRank.lean — theorem BookProof.ChapterAttentionLowRank.scoreMatrix_apply
import Mathlib
import Definitions.Def_ChapterAttentionLowRank
open BookProof.ChapterAttentionLowRank


open scoped BigOperators

noncomputable section


variable {m d : ℕ}

theorem BookProof.ChapterAttentionLowRank.scoreMatrix_apply (Q K : Fin m → Fin d → ℝ) (i j : Fin m) :
    scoreMatrix Q K i j = ∑ a, Q i a * K j a := by sorry
