-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianAtomicCondensation_atomic_abelian_maximal_eq_diagonal
-- name    : BookProof.ChapterAbelianAtomicCondensation.atomic_abelian_maximal_eq_diagonal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:49:42.394979+00:00
-- url     : https://prove2.me/theorems/e9432ae8-d898-4181-b1e5-fd7feb2b496f
-- title:
--   `BookProof.ChapterAbelianAtomicCondensation.atomic_abelian_maximal_eq_diagonal` {A : Set (Ell2C →L[ℂ] Ell2C)} (hA : IsAtomicAbelian A) (hmax : ∀ T : Ell2C →L[ℂ] Ell2C, (∀ S ∈ A, T.
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianAtomicCondensation`.
--
--   `BookProof.ChapterAbelianAtomicCondensation.atomic_abelian_maximal_eq_diagonal` {A : Set (Ell2C →L[ℂ] Ell2C)} (hA : IsAtomicAbelian A) (hmax : ∀ T : Ell2C →L[ℂ] Ell2C, (∀ S ∈ A, T.comp S = S.comp T) → T ∈ A) : A = Set.range diagOp
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianAtomicCondensation.atomic_abelian_maximal_eq_diagonal`.

-- Generated from ChapterAbelianAtomicCondensation.lean — theorem BookProof.ChapterAbelianAtomicCondensation.atomic_abelian_maximal_eq_diagonal
import Mathlib
import Definitions.Def_ChapterAbelianAtomicCondensation
import Definitions.Def_ChapterAbelianDiagonalCountable
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.ChapterAbelianAtomicCondensation


open scoped ENNReal

noncomputable section


open BookProof.ChapterAbelianDiagonalCountable

theorem BookProof.ChapterAbelianAtomicCondensation.atomic_abelian_maximal_eq_diagonal {A : Set (Ell2C →L[ℂ] Ell2C)}
    (hA : IsAtomicAbelian A)
    (hmax : ∀ T : Ell2C →L[ℂ] Ell2C, (∀ S ∈ A, T.comp S = S.comp T) → T ∈ A) :
    A = Set.range diagOp := by sorry
