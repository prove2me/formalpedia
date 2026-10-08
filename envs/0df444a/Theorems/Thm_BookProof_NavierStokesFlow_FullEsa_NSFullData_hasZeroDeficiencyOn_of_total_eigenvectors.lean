-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_NSFullData_hasZeroDeficiencyOn_of_total_eigenvectors
-- name    : BookProof.NavierStokesFlow.FullEsa.NSFullData.hasZeroDeficiencyOn_of_total_eigenvectors
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T11:52:36.525747+00:00
-- url     : https://prove2.me/theorems/7a3428f8-54f4-426e-875b-9ce4f0bcbb46
-- title:
--   `BookProof.NavierStokesFlow.FullEsa.NSFullData.hasZeroDeficiencyOn_of_total_eigenvectors` {I : Type*} (e : I → d.D) (lam : I → ℝ) (heig : ∀ i, d.hamiltonian (e i) = ((lam i : ℂ)) •
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFullEsa`.
--
--   `BookProof.NavierStokesFlow.FullEsa.NSFullData.hasZeroDeficiencyOn_of_total_eigenvectors` {I : Type*} (e : I → d.D) (lam : I → ℝ) (heig : ∀ i, d.hamiltonian (e i) = ((lam i : ℂ)) • e i) (htotal : ∀ w : F, (∀ i, (inner ℂ ((e i : F)) w : ℂ) = 0) → w = 0) : HasZeroDeficiencyOn d.D d.hamiltonian
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FullEsa.NSFullData.hasZeroDeficiencyOn_of_total_eigenvectors`.

-- Generated from ChapterNavierStokesFullEsa.lean — theorem BookProof.NavierStokesFlow.FullEsa.NSFullData.hasZeroDeficiencyOn_of_total_eigenvectors
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa


open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable (d : NSFullData F)

theorem BookProof.NavierStokesFlow.FullEsa.NSFullData.hasZeroDeficiencyOn_of_total_eigenvectors {I : Type*} (e : I → d.D) (lam : I → ℝ)
    (heig : ∀ i, d.hamiltonian (e i) = ((lam i : ℂ)) • e i)
    (htotal : ∀ w : F, (∀ i, (inner ℂ ((e i : F)) w : ℂ) = 0) → w = 0) :
    HasZeroDeficiencyOn d.D d.hamiltonian := by sorry
