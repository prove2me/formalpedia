-- Prove2me | Theorems.Thm_BookProof_ChapterContinuityUnitaryInfinite_bornRecover_mono
-- name    : BookProof.ChapterContinuityUnitaryInfinite.bornRecover_mono
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:08:59.013786+00:00
-- url     : https://prove2.me/theorems/d8e4f128-faf4-44fd-b20c-f15e5b53c47c
-- title:
--   (v : LinfZ) (t : ℝ) (psi : L2Z) {B C : Finset ℤ} (h : B ⊆ C) : bornRecover v t psi B ≤ bornRecover v t psi C
-- statement:
--   Lean 4 theorem `BookProof.ChapterContinuityUnitaryInfinite.bornRecover_mono` (module `BookProof.ChapterContinuityUnitaryInfinite`), source chapter `BookProof/ChapterChapterContinuityUnitaryInfinite.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterContinuityUnitaryInfinite.lean

-- Generated from ChapterContinuityUnitaryInfinite.lean — theorem BookProof.ChapterContinuityUnitaryInfinite.bornRecover_mono
import Mathlib
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterContinuityUnitaryInfinite







open scoped ENNReal InnerProductSpace

theorem BookProof.ChapterContinuityUnitaryInfinite.bornRecover_mono (v : LinfZ) (t : ℝ) (psi : L2Z) {B C : Finset ℤ} (h : B ⊆ C) :
    bornRecover v t psi B ≤ bornRecover v t psi C := by sorry
