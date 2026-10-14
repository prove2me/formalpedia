-- Prove2me | Theorems.Thm_BookProof_WeylHamiltonian_weylHamiltonian_isPositive
-- name    : BookProof.WeylHamiltonian.weylHamiltonian_isPositive
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T20:41:07.261582+00:00
-- url     : https://prove2.me/theorems/a2a6da78-25ea-4686-b877-0bcfd391cc3a
-- title:
--   `BookProof.WeylHamiltonian.weylHamiltonian_isPositive` {n m : ℕ} (π : Fin n → H →L[ℂ] H) (B : Fin m → H →L[ℂ] H) (hπ : ∀ i, IsSelfAdjoint (π i)) (hB : ∀ a, IsSelfAdjoint (B...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylHamiltonian`.
--
--   `BookProof.WeylHamiltonian.weylHamiltonian_isPositive` {n m : ℕ} (π : Fin n → H →L[ℂ] H) (B : Fin m → H →L[ℂ] H) (hπ : ∀ i, IsSelfAdjoint (π i)) (hB : ∀ a, IsSelfAdjoint (B a)) : (weylHamiltonian π B).IsPositive
--
--   Formalization note: Lean 4 identifier `BookProof.WeylHamiltonian.weylHamiltonian_isPositive`.

-- Generated from ChapterWeylHamiltonian.lean — theorem BookProof.WeylHamiltonian.weylHamiltonian_isPositive
import Mathlib
import Definitions.Def_ChapterWeylHamiltonian
open BookProof.WeylHamiltonian



open ContinuousLinearMap
open scoped BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem BookProof.WeylHamiltonian.weylHamiltonian_isPositive {n m : ℕ}
    (π : Fin n → H →L[ℂ] H) (B : Fin m → H →L[ℂ] H)
    (hπ : ∀ i, IsSelfAdjoint (π i)) (hB : ∀ a, IsSelfAdjoint (B a)) :
    (weylHamiltonian π B).IsPositive := by sorry
