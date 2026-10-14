-- Prove2me | Theorems.Thm_BookProof_WeylHamiltonian_weylHamiltonian_isSelfAdjoint
-- name    : BookProof.WeylHamiltonian.weylHamiltonian_isSelfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T20:40:17.945333+00:00
-- url     : https://prove2.me/theorems/4c9a2f03-90dc-4c9a-b595-031ee680ad68
-- title:
--   `BookProof.WeylHamiltonian.weylHamiltonian_isSelfAdjoint` {n m : ℕ} (π : Fin n → H →L[ℂ] H) (B : Fin m → H →L[ℂ] H) (hπ : ∀ i, IsSelfAdjoint (π i)) (hB : ∀ a, IsSelfAdjoint (B a))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylHamiltonian`.
--
--   `BookProof.WeylHamiltonian.weylHamiltonian_isSelfAdjoint` {n m : ℕ} (π : Fin n → H →L[ℂ] H) (B : Fin m → H →L[ℂ] H) (hπ : ∀ i, IsSelfAdjoint (π i)) (hB : ∀ a, IsSelfAdjoint (B a)) : IsSelfAdjoint (weylHamiltonian π B)
--
--   Formalization note: Lean 4 identifier `BookProof.WeylHamiltonian.weylHamiltonian_isSelfAdjoint`.

-- Generated from ChapterWeylHamiltonian.lean — theorem BookProof.WeylHamiltonian.weylHamiltonian_isSelfAdjoint
import Mathlib
import Definitions.Def_ChapterWeylHamiltonian
open BookProof.WeylHamiltonian



open ContinuousLinearMap
open scoped BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem BookProof.WeylHamiltonian.weylHamiltonian_isSelfAdjoint {n m : ℕ}
    (π : Fin n → H →L[ℂ] H) (B : Fin m → H →L[ℂ] H)
    (hπ : ∀ i, IsSelfAdjoint (π i)) (hB : ∀ a, IsSelfAdjoint (B a)) :
    IsSelfAdjoint (weylHamiltonian π B) := by sorry
