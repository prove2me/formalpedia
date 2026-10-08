-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianAtomicCondensation_commutes_atomProj_iff
-- name    : BookProof.ChapterAbelianAtomicCondensation.commutes_atomProj_iff
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:16:47.304351+00:00
-- url     : https://prove2.me/theorems/8b3a7d4f-7229-4d3f-ae70-8fd3a451222b
-- title:
--   `BookProof.ChapterAbelianAtomicCondensation.commutes_atomProj_iff` (T : Ell2C →L[ℂ] Ell2C) : (∀ i : ℕ, T.comp (atomProj i) = (atomProj i).comp T) ↔ ∃ d : EllInf, T = diagOp d
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianAtomicCondensation`.
--
--   `BookProof.ChapterAbelianAtomicCondensation.commutes_atomProj_iff` (T : Ell2C →L[ℂ] Ell2C) : (∀ i : ℕ, T.comp (atomProj i) = (atomProj i).comp T) ↔ ∃ d : EllInf, T = diagOp d
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianAtomicCondensation.commutes_atomProj_iff`.

-- Generated from ChapterAbelianAtomicCondensation.lean — theorem BookProof.ChapterAbelianAtomicCondensation.commutes_atomProj_iff
import Mathlib
import Definitions.Def_ChapterAbelianAtomicCondensation
import Definitions.Def_ChapterAbelianDiagonalCountable
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.ChapterAbelianAtomicCondensation


open scoped ENNReal

noncomputable section


open BookProof.ChapterAbelianDiagonalCountable

theorem BookProof.ChapterAbelianAtomicCondensation.commutes_atomProj_iff (T : Ell2C →L[ℂ] Ell2C) :
    (∀ i : ℕ, T.comp (atomProj i) = (atomProj i).comp T) ↔ ∃ d : EllInf, T = diagOp d := by sorry
