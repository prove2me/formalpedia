-- Prove2me | Theorems.Thm_BookProof_ChapterSchurFiniteDim_schur_scalar_of_irreducible
-- name    : BookProof.ChapterSchurFiniteDim.schur_scalar_of_irreducible
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:59:39.219973+00:00
-- url     : https://prove2.me/theorems/cd45ae40-9898-473e-9331-02b6d1ce36f3
-- title:
--   `BookProof.ChapterSchurFiniteDim.schur_scalar_of_irreducible` [FiniteDimensional ℂ V] [Nontrivial V] (M : System ℂ V) (hirr : IsIrreducibleSystem M) (f : V →ₗ[ℂ] V) (hf : ∀ m ∈ M.o
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSchurFiniteDim`.
--
--   `BookProof.ChapterSchurFiniteDim.schur_scalar_of_irreducible` [FiniteDimensional ℂ V] [Nontrivial V] (M : System ℂ V) (hirr : IsIrreducibleSystem M) (f : V →ₗ[ℂ] V) (hf : ∀ m ∈ M.ops, ∀ x, f (m x) = m (f x)) : ∃ c : ℂ, ∀ x, f x = c • x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSchurFiniteDim.schur_scalar_of_irreducible`.

-- Generated from ChapterSchurFiniteDim.lean — theorem BookProof.ChapterSchurFiniteDim.schur_scalar_of_irreducible
import Mathlib
import Definitions.Def_ChapterSchurFiniteDim
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA
open BookProof.ChapterSchurFiniteDim


open Module


open BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterSchurFiniteDim.schur_scalar_of_irreducible [FiniteDimensional ℂ V] [Nontrivial V]
    (M : System ℂ V) (hirr : IsIrreducibleSystem M) (f : V →ₗ[ℂ] V)
    (hf : ∀ m ∈ M.ops, ∀ x, f (m x) = m (f x)) :
    ∃ c : ℂ, ∀ x, f x = c • x := by sorry
