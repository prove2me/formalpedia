-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianDiagonalCountable_vonNeumann_abelian_class_countable
-- name    : BookProof.ChapterAbelianDiagonalCountable.vonNeumann_abelian_class_countable
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:18:46.034977+00:00
-- url     : https://prove2.me/theorems/4beae014-955d-402d-b6dc-73be59d0f8ef
-- title:
--   `BookProof.ChapterAbelianDiagonalCountable.vonNeumann_abelian_class_countable` : Function.Injective diagOp ∧ (∀ d e : EllInf, (diagOp d).comp (diagOp e) = (diagOp e).comp (diagOp d
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianDiagonalCountable`.
--
--   `BookProof.ChapterAbelianDiagonalCountable.vonNeumann_abelian_class_countable` : Function.Injective diagOp ∧ (∀ d e : EllInf, (diagOp d).comp (diagOp e) = (diagOp e).comp (diagOp d)) ∧ (∀ T : Ell2C →L[ℂ] Ell2C, (∀ d : EllInf, T.comp (diagOp d) = (diagOp d).comp T) ↔ ∃ d : EllInf, T = diagOp d)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianDiagonalCountable.vonNeumann_abelian_class_countable`.

-- Generated from ChapterAbelianDiagonalCountable.lean — theorem BookProof.ChapterAbelianDiagonalCountable.vonNeumann_abelian_class_countable
import Mathlib
import Definitions.Def_ChapterAbelianDiagonalCountable
open BookProof.ChapterAbelianDiagonalCountable


open scoped ENNReal

noncomputable section

theorem BookProof.ChapterAbelianDiagonalCountable.vonNeumann_abelian_class_countable :
    Function.Injective diagOp ∧
      (∀ d e : EllInf, (diagOp d).comp (diagOp e) = (diagOp e).comp (diagOp d)) ∧
      (∀ T : Ell2C →L[ℂ] Ell2C,
        (∀ d : EllInf, T.comp (diagOp d) = (diagOp d).comp T) ↔ ∃ d : EllInf, T = diagOp d) := by sorry
