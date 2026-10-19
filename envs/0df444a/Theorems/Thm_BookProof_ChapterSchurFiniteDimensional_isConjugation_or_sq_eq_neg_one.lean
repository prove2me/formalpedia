-- Prove2me | Theorems.Thm_BookProof_ChapterSchurFiniteDimensional_isConjugation_or_sq_eq_neg_one
-- name    : BookProof.ChapterSchurFiniteDimensional.isConjugation_or_sq_eq_neg_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:00:29.759978+00:00
-- url     : https://prove2.me/theorems/dabcc326-506b-4538-abf4-cd9aec797892
-- title:
--   `BookProof.ChapterSchurFiniteDimensional.isConjugation_or_sq_eq_neg_one` [FiniteDimensional ℂ V] [Nontrivial V] (M : System ℂ V) (hirr : M.IsIrreducible) {θ : AntiUnitary V} (hθ :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSchurFiniteDimensional`.
--
--   `BookProof.ChapterSchurFiniteDimensional.isConjugation_or_sq_eq_neg_one` [FiniteDimensional ℂ V] [Nontrivial V] (M : System ℂ V) (hirr : M.IsIrreducible) {θ : AntiUnitary V} (hθ : CommutesAntiUnitary M θ) : IsConjugation M θ ∨ ((∀ x, θ (θ x) = -x) ∧ ∀ m ∈ M.ops, ∀ x, θ (m x) = m (θ x))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSchurFiniteDimensional.isConjugation_or_sq_eq_neg_one`.

-- Generated from ChapterSchurFiniteDimensional.lean — theorem BookProof.ChapterSchurFiniteDimensional.isConjugation_or_sq_eq_neg_one
import Mathlib
import Definitions.Def_ChapterSchurFiniteDimensional
import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
open BookProof.ChapterA
open BookProof.ChapterA
open BookProof.ChapterA
open BookProof.ChapterSchurFiniteDimensional


open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterSchurFiniteDimensional.isConjugation_or_sq_eq_neg_one [FiniteDimensional ℂ V] [Nontrivial V]
    (M : System ℂ V) (hirr : M.IsIrreducible) {θ : AntiUnitary V}
    (hθ : CommutesAntiUnitary M θ) :
    IsConjugation M θ ∨ ((∀ x, θ (θ x) = -x) ∧ ∀ m ∈ M.ops, ∀ x, θ (m x) = m (θ x)) := by sorry
