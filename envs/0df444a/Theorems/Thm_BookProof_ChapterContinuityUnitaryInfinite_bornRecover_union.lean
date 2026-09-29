-- Prove2me | Theorems.Thm_BookProof_ChapterContinuityUnitaryInfinite_bornRecover_union
-- name    : BookProof.ChapterContinuityUnitaryInfinite.bornRecover_union
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:10:10.365398+00:00
-- url     : https://prove2.me/theorems/c8299705-b54d-4bf5-8966-a79bfb2b15a2
-- title:
--   (v : LinfZ) (t : ℝ) (psi : L2Z) {B C : Finset ℤ} (h : Disjoint B C) : bornRecover v t psi (B ∪ C) = bornRecover v t psi B + bornRecover v t psi C
-- statement:
--   Lean 4 theorem `BookProof.ChapterContinuityUnitaryInfinite.bornRecover_union` (module `BookProof.ChapterContinuityUnitaryInfinite`), source chapter `BookProof/ChapterChapterContinuityUnitaryInfinite.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterContinuityUnitaryInfinite.lean

-- Generated from ChapterContinuityUnitaryInfinite.lean — theorem BookProof.ChapterContinuityUnitaryInfinite.bornRecover_union
import Mathlib
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterContinuityUnitaryInfinite







open scoped ENNReal InnerProductSpace

theorem BookProof.ChapterContinuityUnitaryInfinite.bornRecover_union (v : LinfZ) (t : ℝ) (psi : L2Z) {B C : Finset ℤ}
    (h : Disjoint B C) :
    bornRecover v t psi (B ∪ C) = bornRecover v t psi B + bornRecover v t psi C := by sorry
