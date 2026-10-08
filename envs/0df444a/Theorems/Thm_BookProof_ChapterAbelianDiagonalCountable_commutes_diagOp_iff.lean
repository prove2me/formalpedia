-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianDiagonalCountable_commutes_diagOp_iff
-- name    : BookProof.ChapterAbelianDiagonalCountable.commutes_diagOp_iff
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:18:40.858396+00:00
-- url     : https://prove2.me/theorems/48bc84f3-fdd6-4f55-9bb8-789160be1eae
-- title:
--   `BookProof.ChapterAbelianDiagonalCountable.commutes_diagOp_iff` (T : Ell2C →L[ℂ] Ell2C) : (∀ d : EllInf, T.comp (diagOp d) = (diagOp d).comp T) ↔ ∃ d : EllInf, T = diagOp d
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianDiagonalCountable`.
--
--   `BookProof.ChapterAbelianDiagonalCountable.commutes_diagOp_iff` (T : Ell2C →L[ℂ] Ell2C) : (∀ d : EllInf, T.comp (diagOp d) = (diagOp d).comp T) ↔ ∃ d : EllInf, T = diagOp d
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianDiagonalCountable.commutes_diagOp_iff`.

-- Generated from ChapterAbelianDiagonalCountable.lean — theorem BookProof.ChapterAbelianDiagonalCountable.commutes_diagOp_iff
import Mathlib
import Definitions.Def_ChapterAbelianDiagonalCountable
open BookProof.ChapterAbelianDiagonalCountable


open scoped ENNReal

noncomputable section

theorem BookProof.ChapterAbelianDiagonalCountable.commutes_diagOp_iff (T : Ell2C →L[ℂ] Ell2C) :
    (∀ d : EllInf, T.comp (diagOp d) = (diagOp d).comp T) ↔ ∃ d : EllInf, T = diagOp d := by sorry
