-- Prove2me | Theorems.Thm_BookProof_ChapterH4_sirk_le_sia
-- name    : BookProof.ChapterH4.sirk_le_sia
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:20:58.457702+00:00
-- url     : https://prove2.me/theorems/f3e40d47-c36b-4652-b742-433dbf87d75d
-- title:
--   (C Dmin h m normv : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ Dmin) (hnv : 0 ≤ normv) (hh : 0 ≤ h) (hm : 0 ≤ m) : 2 * C * Real.exp (-(h * m)) * Dmin * normv ≤ 2 * C * Dmin * normv
-- statement:
--   Lean 4 theorem `BookProof.ChapterH4.sirk_le_sia` (module `BookProof.ChapterH4`), source chapter `BookProof/ChapterChapterH4.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterH4.lean

-- Generated from ChapterH4.lean — theorem BookProof.ChapterH4.sirk_le_sia
import Mathlib
import Definitions.Def_ChapterH4
open BookProof.ChapterH4









open scoped BigOperators


noncomputable section





variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterH4.sirk_le_sia (C Dmin h m normv : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ Dmin) (hnv : 0 ≤ normv)
    (hh : 0 ≤ h) (hm : 0 ≤ m) :
    2 * C * Real.exp (-(h * m)) * Dmin * normv ≤ 2 * C * Dmin * normv := by sorry
