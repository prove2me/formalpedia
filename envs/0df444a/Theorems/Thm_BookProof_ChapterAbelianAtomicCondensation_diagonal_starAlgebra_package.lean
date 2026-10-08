-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianAtomicCondensation_diagonal_starAlgebra_package
-- name    : BookProof.ChapterAbelianAtomicCondensation.diagonal_starAlgebra_package
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:49:38.813492+00:00
-- url     : https://prove2.me/theorems/4a53437e-2add-470d-b31f-e19c81b19e73
-- title:
--   `BookProof.ChapterAbelianAtomicCondensation.diagonal_starAlgebra_package` : Function.Injective diagOp ∧ (∀ d e : EllInf, diagOp (d * e) = (diagOp d).comp (diagOp e)) ∧ diagOp (1 :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianAtomicCondensation`.
--
--   `BookProof.ChapterAbelianAtomicCondensation.diagonal_starAlgebra_package` : Function.Injective diagOp ∧ (∀ d e : EllInf, diagOp (d * e) = (diagOp d).comp (diagOp e)) ∧ diagOp (1 : EllInf) = ContinuousLinearMap.id ℂ Ell2C ∧ (∀ d : EllInf, ∀ f g : Ell2C, (inner ℂ (diagOp d f) g : ℂ) = (inner ℂ f (diagOp (star d) g) : ℂ))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianAtomicCondensation.diagonal_starAlgebra_package`.

-- Generated from ChapterAbelianAtomicCondensation.lean — theorem BookProof.ChapterAbelianAtomicCondensation.diagonal_starAlgebra_package
import Mathlib
import Definitions.Def_ChapterAbelianAtomicCondensation
import Definitions.Def_ChapterAbelianDiagonalCountable
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.ChapterAbelianAtomicCondensation


open scoped ENNReal

noncomputable section


open BookProof.ChapterAbelianDiagonalCountable

theorem BookProof.ChapterAbelianAtomicCondensation.diagonal_starAlgebra_package :
    Function.Injective diagOp ∧
      (∀ d e : EllInf, diagOp (d * e) = (diagOp d).comp (diagOp e)) ∧
      diagOp (1 : EllInf) = ContinuousLinearMap.id ℂ Ell2C ∧
      (∀ d : EllInf, ∀ f g : Ell2C,
        (inner ℂ (diagOp d f) g : ℂ) = (inner ℂ f (diagOp (star d) g) : ℂ)) := by sorry
