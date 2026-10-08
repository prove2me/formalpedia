-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianAtomicCondensation_atomic_abelian_subset_diagonal
-- name    : BookProof.ChapterAbelianAtomicCondensation.atomic_abelian_subset_diagonal
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:16:38.01742+00:00
-- url     : https://prove2.me/theorems/96d2f728-8130-4029-bf7e-e141587717a7
-- title:
--   `BookProof.ChapterAbelianAtomicCondensation.atomic_abelian_subset_diagonal` {A : Set (Ell2C →L[ℂ] Ell2C)} (hA : IsAtomicAbelian A) : A ⊆ Set.range diagOp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianAtomicCondensation`.
--
--   `BookProof.ChapterAbelianAtomicCondensation.atomic_abelian_subset_diagonal` {A : Set (Ell2C →L[ℂ] Ell2C)} (hA : IsAtomicAbelian A) : A ⊆ Set.range diagOp
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianAtomicCondensation.atomic_abelian_subset_diagonal`.

-- Generated from ChapterAbelianAtomicCondensation.lean — theorem BookProof.ChapterAbelianAtomicCondensation.atomic_abelian_subset_diagonal
import Mathlib
import Definitions.Def_ChapterAbelianAtomicCondensation
import Definitions.Def_ChapterAbelianDiagonalCountable
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.ChapterAbelianAtomicCondensation


open scoped ENNReal

noncomputable section


open BookProof.ChapterAbelianDiagonalCountable

theorem BookProof.ChapterAbelianAtomicCondensation.atomic_abelian_subset_diagonal {A : Set (Ell2C →L[ℂ] Ell2C)}
    (hA : IsAtomicAbelian A) : A ⊆ Set.range diagOp := by sorry
