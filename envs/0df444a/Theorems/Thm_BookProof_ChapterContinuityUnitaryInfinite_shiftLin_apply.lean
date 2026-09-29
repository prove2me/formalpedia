-- Prove2me | Theorems.Thm_BookProof_ChapterContinuityUnitaryInfinite_shiftLin_apply
-- name    : BookProof.ChapterContinuityUnitaryInfinite.shiftLin_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:12:58.656748+00:00
-- url     : https://prove2.me/theorems/76fb05fb-d48e-4900-a87d-2b4e1943872c
-- title:
--   (m : ℤ) (f : L2Z) (k : ℤ) : ((shiftLin m f : L2Z) : ℤ → ℂ) k = (f : ℤ → ℂ) (k + m)
-- statement:
--   Lean 4 theorem `BookProof.ChapterContinuityUnitaryInfinite.shiftLin_apply` (module `BookProof.ChapterContinuityUnitaryInfinite`), source chapter `BookProof/ChapterChapterContinuityUnitaryInfinite.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterContinuityUnitaryInfinite.lean

-- Generated from ChapterContinuityUnitaryInfinite.lean — theorem BookProof.ChapterContinuityUnitaryInfinite.shiftLin_apply
import Mathlib
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterContinuityUnitaryInfinite







open scoped ENNReal InnerProductSpace

theorem BookProof.ChapterContinuityUnitaryInfinite.shiftLin_apply (m : ℤ) (f : L2Z) (k : ℤ) :
    ((shiftLin m f : L2Z) : ℤ → ℂ) k = (f : ℤ → ℂ) (k + m) := by sorry
