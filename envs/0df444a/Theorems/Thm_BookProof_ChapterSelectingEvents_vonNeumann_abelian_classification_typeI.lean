-- Prove2me | Theorems.Thm_BookProof_ChapterSelectingEvents_vonNeumann_abelian_classification_typeI
-- name    : BookProof.ChapterSelectingEvents.vonNeumann_abelian_classification_typeI
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T11:45:39.230278+00:00
-- url     : https://prove2.me/theorems/cac736f7-beeb-499f-9743-13df3d1ce975
-- title:
--   `BookProof.ChapterSelectingEvents.vonNeumann_abelian_classification_typeI` {ι : Type*} [Fintype ι] [DecidableEq ι] : Function.Injective (BookProof.AbelianDiagonal.diagonalStarAlgHo
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSelectingEvents`.
--
--   `BookProof.ChapterSelectingEvents.vonNeumann_abelian_classification_typeI` {ι : Type*} [Fintype ι] [DecidableEq ι] : Function.Injective (BookProof.AbelianDiagonal.diagonalStarAlgHom : (ι → ℂ) →⋆ₐ[ℂ] Matrix ι ι ℂ) ∧ (∀ d e : ι → ℂ, Matrix.diagonal d * Matrix.diagonal e = Matrix.diagonal e * Matrix.diagonal d) ∧ (∀ M : Matrix ι ι ℂ, (∀ d : ι → ℂ, M * Matrix.diagonal d = Matrix.diagonal d * M) ↔ ∃ e : ι → ℂ, M = Matrix.diagonal e)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSelectingEvents.vonNeumann_abelian_classification_typeI`.

-- Generated from ChapterSelectingEvents.lean — theorem BookProof.ChapterSelectingEvents.vonNeumann_abelian_classification_typeI
import Mathlib
import Definitions.Def_ChapterSelectingEvents
import Definitions.Def_ChapterAbelianDiagonal
open BookProof.AbelianDiagonal
open BookProof.ChapterSelectingEvents


open scoped BigOperators
open MeasureTheory ProbabilityTheory


variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {Ω Data : Type*} [MeasurableSpace Ω]

theorem BookProof.ChapterSelectingEvents.vonNeumann_abelian_classification_typeI
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Function.Injective
        (BookProof.AbelianDiagonal.diagonalStarAlgHom :
          (ι → ℂ) →⋆ₐ[ℂ] Matrix ι ι ℂ) ∧
      (∀ d e : ι → ℂ,
        Matrix.diagonal d * Matrix.diagonal e = Matrix.diagonal e * Matrix.diagonal d) ∧
      (∀ M : Matrix ι ι ℂ,
        (∀ d : ι → ℂ, M * Matrix.diagonal d = Matrix.diagonal d * M) ↔
          ∃ e : ι → ℂ, M = Matrix.diagonal e) := by sorry
