-- Prove2me | Theorems.Thm_BookProof_ChapterSchurFiniteDimensional_antiUnitary_sq_of_irreducible_finiteDimensional
-- name    : BookProof.ChapterSchurFiniteDimensional.antiUnitary_sq_of_irreducible_finiteDimensional
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:00:38.685979+00:00
-- url     : https://prove2.me/theorems/eeba0483-863a-4e6d-b374-bb2e80494aa0
-- title:
--   `BookProof.ChapterSchurFiniteDimensional.antiUnitary_sq_of_irreducible_finiteDimensional` [FiniteDimensional ℂ V] [Nontrivial V] (M : System ℂ V) (hirr : M.IsIrreducible) {θ : Anti
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSchurFiniteDimensional`.
--
--   `BookProof.ChapterSchurFiniteDimensional.antiUnitary_sq_of_irreducible_finiteDimensional` [FiniteDimensional ℂ V] [Nontrivial V] (M : System ℂ V) (hirr : M.IsIrreducible) {θ : AntiUnitary V} (hθ : CommutesAntiUnitary M θ) : (∀ x, θ (θ x) = x) ∨ (∀ x, θ (θ x) = -x)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSchurFiniteDimensional.antiUnitary_sq_of_irreducible_finiteDimensional`.

-- Generated from ChapterSchurFiniteDimensional.lean — theorem BookProof.ChapterSchurFiniteDimensional.antiUnitary_sq_of_irreducible_finiteDimensional
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

theorem BookProof.ChapterSchurFiniteDimensional.antiUnitary_sq_of_irreducible_finiteDimensional [FiniteDimensional ℂ V] [Nontrivial V]
    (M : System ℂ V) (hirr : M.IsIrreducible) {θ : AntiUnitary V}
    (hθ : CommutesAntiUnitary M θ) :
    (∀ x, θ (θ x) = x) ∨ (∀ x, θ (θ x) = -x) := by sorry
