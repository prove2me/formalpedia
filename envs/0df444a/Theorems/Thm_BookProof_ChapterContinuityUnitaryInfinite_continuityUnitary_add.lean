-- Prove2me | Theorems.Thm_BookProof_ChapterContinuityUnitaryInfinite_continuityUnitary_add
-- name    : BookProof.ChapterContinuityUnitaryInfinite.continuityUnitary_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:10:43.814933+00:00
-- url     : https://prove2.me/theorems/c5b80ce5-e01b-416e-8f5a-0f502111dfa3
-- title:
--   (v : LinfZ) (s t : ℝ) : continuityUnitary v (s + t) = continuityUnitary v s * continuityUnitary v t
-- statement:
--   Lean 4 theorem `BookProof.ChapterContinuityUnitaryInfinite.continuityUnitary_add` (module `BookProof.ChapterContinuityUnitaryInfinite`), source chapter `BookProof/ChapterChapterContinuityUnitaryInfinite.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterContinuityUnitaryInfinite.lean

-- Generated from ChapterContinuityUnitaryInfinite.lean — theorem BookProof.ChapterContinuityUnitaryInfinite.continuityUnitary_add
import Mathlib
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterContinuityUnitaryInfinite







open scoped ENNReal InnerProductSpace

theorem BookProof.ChapterContinuityUnitaryInfinite.continuityUnitary_add (v : LinfZ) (s t : ℝ) :
    continuityUnitary v (s + t) = continuityUnitary v s * continuityUnitary v t := by sorry
