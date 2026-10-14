-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_nsFullData_hasZeroDeficiencyOn_of_fockLagrangian
-- name    : BookProof.NavierStokesFlow.FockOfFock.nsFullData_hasZeroDeficiencyOn_of_fockLagrangian
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T19:18:15.346614+00:00
-- url     : https://prove2.me/theorems/ae7e9447-cb5f-41df-83a3-3d31f4e9059b
-- title:
--   `BookProof.NavierStokesFlow.FockOfFock.nsFullData_hasZeroDeficiencyOn_of_fockLagrangian` (d : FullEsa.NSFullData F) (nu : ℝ) (hnu : 0 ≤ nu) (p q dr : Fin 3 → M → ℝ) (force : Fin 3
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockEsa`.
--
--   `BookProof.NavierStokesFlow.FockOfFock.nsFullData_hasZeroDeficiencyOn_of_fockLagrangian` (d : FullEsa.NSFullData F) (nu : ℝ) (hnu : 0 ≤ nu) (p q dr : Fin 3 → M → ℝ) (force : Fin 3 → ℝ) (cst : M → ℝ) (W : F ≃ₗᵢ[ℂ] FockL2 M) (hmap : ∀ x : d.D, W (x : F) ∈ (lagrangianFockData nu hnu p q dr force cst).D) (hsurj : ∀ y : (lagrangianFockData nu hnu p q dr force cst).D, ∃ x : d.D, W (x : F) = (y : FockL2 M)) (hint : ∀ x : d.D, ((lagrangianFockData nu hnu p q dr force cst).hFull ⟨W (x : F), hmap x⟩ : FockL2 M) = W ((d.hamiltonian x : F))) : HasZeroDeficiencyOn d.D d.hamiltonian
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockOfFock.nsFullData_hasZeroDeficiencyOn_of_fockLagrangian`.

-- Generated from ChapterNavierStokesFockEsa.lean — theorem BookProof.NavierStokesFlow.FockOfFock.nsFullData_hasZeroDeficiencyOn_of_fockLagrangian
import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow.FockOfFock
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa.NSFullData
open BookProof.NavierStokesFlow


open MeasureTheory



open FullEsa LagrangianEsa

variable {M : Type*} [DecidableEq M]
variable {M : Type*} [DecidableEq M] {Ω : Type*} [MeasurableSpace Ω]
variable {J K : Type*} [DecidableEq J] [DecidableEq K]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.NavierStokesFlow.FockOfFock.nsFullData_hasZeroDeficiencyOn_of_fockLagrangian (d : FullEsa.NSFullData F) (nu : ℝ)
    (hnu : 0 ≤ nu) (p q dr : Fin 3 → M → ℝ) (force : Fin 3 → ℝ) (cst : M → ℝ)
    (W : F ≃ₗᵢ[ℂ] FockL2 M)
    (hmap : ∀ x : d.D, W (x : F) ∈ (lagrangianFockData nu hnu p q dr force cst).D)
    (hsurj : ∀ y : (lagrangianFockData nu hnu p q dr force cst).D,
      ∃ x : d.D, W (x : F) = (y : FockL2 M))
    (hint : ∀ x : d.D, ((lagrangianFockData nu hnu p q dr force cst).hFull
        ⟨W (x : F), hmap x⟩ : FockL2 M) = W ((d.hamiltonian x : F))) :
    HasZeroDeficiencyOn d.D d.hamiltonian := by sorry
