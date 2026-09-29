-- Prove2me | Theorems.Thm_BookProof_ChapterContinuityUnitaryInfinite_velocityLin_apply
-- name    : BookProof.ChapterContinuityUnitaryInfinite.velocityLin_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:13:33.279745+00:00
-- url     : https://prove2.me/theorems/1ab16983-7039-4fca-bcc0-7e7f5b281b35
-- title:
--   (v : LinfZ) (f : L2Z) (k : ℤ) : ((velocityLin v f : L2Z) : ℤ → ℂ) k = ((v : ℤ → ℝ) k : ℂ) * (f : ℤ → ℂ) k
-- statement:
--   Lean 4 theorem `BookProof.ChapterContinuityUnitaryInfinite.velocityLin_apply` (module `BookProof.ChapterContinuityUnitaryInfinite`), source chapter `BookProof/ChapterChapterContinuityUnitaryInfinite.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterContinuityUnitaryInfinite.lean

-- Generated from ChapterContinuityUnitaryInfinite.lean — theorem BookProof.ChapterContinuityUnitaryInfinite.velocityLin_apply
import Mathlib
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterContinuityUnitaryInfinite







open scoped ENNReal InnerProductSpace

theorem BookProof.ChapterContinuityUnitaryInfinite.velocityLin_apply (v : LinfZ) (f : L2Z) (k : ℤ) :
    ((velocityLin v f : L2Z) : ℤ → ℂ) k = ((v : ℤ → ℝ) k : ℂ) * (f : ℤ → ℂ) k := by sorry
