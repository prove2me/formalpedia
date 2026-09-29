-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramWhitening_sum_norm_coord_le
-- name    : BookProof.ChapterSirkGramWhitening.sum_norm_coord_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:29:01.225582+00:00
-- url     : https://prove2.me/theorems/3e27623e-e69a-46a2-b129-e6374c593cdf
-- title:
--   {m : ℕ} (c : EuclideanSpace ℂ (Fin m)) : ∑ i, ‖c i‖ ≤ Real.sqrt m * ‖c‖
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramWhitening.sum_norm_coord_le` (module `BookProof.ChapterSirkGramWhitening`), source chapter `BookProof/ChapterChapterSirkGramWhitening.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramWhitening.lean

-- Generated from ChapterSirkGramWhitening.lean — theorem BookProof.ChapterSirkGramWhitening.sum_norm_coord_le
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening








noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramWhitening.sum_norm_coord_le {m : ℕ} (c : EuclideanSpace ℂ (Fin m)) :
    ∑ i, ‖c i‖ ≤ Real.sqrt m * ‖c‖ := by sorry
