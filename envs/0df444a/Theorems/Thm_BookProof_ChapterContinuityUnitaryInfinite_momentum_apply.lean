-- Prove2me | Theorems.Thm_BookProof_ChapterContinuityUnitaryInfinite_momentum_apply
-- name    : BookProof.ChapterContinuityUnitaryInfinite.momentum_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:11:53.811958+00:00
-- url     : https://prove2.me/theorems/3b83d9cb-5e33-4d5d-8ff6-8a1248a7db67
-- title:
--   (f : L2Z) (k : ℤ) : ((momentum f : L2Z) : ℤ → ℂ) k = (-Complex.I / 2) * ((f : ℤ → ℂ) (k + 1) - (f : ℤ → ℂ) (k - 1))
-- statement:
--   Lean 4 theorem `BookProof.ChapterContinuityUnitaryInfinite.momentum_apply` (module `BookProof.ChapterContinuityUnitaryInfinite`), source chapter `BookProof/ChapterChapterContinuityUnitaryInfinite.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterContinuityUnitaryInfinite.lean

-- Generated from ChapterContinuityUnitaryInfinite.lean — theorem BookProof.ChapterContinuityUnitaryInfinite.momentum_apply
import Mathlib
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterContinuityUnitaryInfinite







open scoped ENNReal InnerProductSpace

theorem BookProof.ChapterContinuityUnitaryInfinite.momentum_apply (f : L2Z) (k : ℤ) :
    ((momentum f : L2Z) : ℤ → ℂ) k
      = (-Complex.I / 2) * ((f : ℤ → ℂ) (k + 1) - (f : ℤ → ℂ) (k - 1)) := by sorry
