-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_NSFullData_hasZeroDeficiencyOn_of_lagrangian
-- name    : BookProof.NavierStokesFlow.LagrangianEsa.NSFullData.hasZeroDeficiencyOn_of_lagrangian
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T12:36:04.029036+00:00
-- url     : https://prove2.me/theorems/a0ccb389-a5ac-48d6-ae21-5c0fbfef358b
-- title:
--   `BookProof.NavierStokesFlow.LagrangianEsa.NSFullData.hasZeroDeficiencyOn_of_lagrangian` (d : FullEsa.NSFullData F) (L : LagrangianFullData G) (W : F ≃ₗᵢ[ℂ] G) (hmap : ∀ x : d.D, W
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesLagrangianEsa`.
--
--   `BookProof.NavierStokesFlow.LagrangianEsa.NSFullData.hasZeroDeficiencyOn_of_lagrangian` (d : FullEsa.NSFullData F) (L : LagrangianFullData G) (W : F ≃ₗᵢ[ℂ] G) (hmap : ∀ x : d.D, W (x : F) ∈ L.D) (hsurj : ∀ y : L.D, ∃ x : d.D, W (x : F) = (y : G)) (hint : ∀ x : d.D, (L.hFull ⟨W (x : F), hmap x⟩ : G) = W ((d.hamiltonian x : F))) (hL : HasZeroDeficiencyOn L.D L.hFull) : HasZeroDeficiencyOn d.D d.hamiltonian
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.LagrangianEsa.NSFullData.hasZeroDeficiencyOn_of_lagrangian`.

-- Generated from ChapterNavierStokesLagrangianEsa.lean — theorem BookProof.NavierStokesFlow.LagrangianEsa.NSFullData.hasZeroDeficiencyOn_of_lagrangian
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_LagrangianFullData_viscous_isSymmetricDom
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa.NSFullData
open BookProof.NavierStokesFlow




open FullEsa
open BookProof.NavierStokesFlow.LagrangianEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)
variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

theorem BookProof.NavierStokesFlow.LagrangianEsa.NSFullData.hasZeroDeficiencyOn_of_lagrangian (d : FullEsa.NSFullData F)
    (L : LagrangianFullData G) (W : F ≃ₗᵢ[ℂ] G) (hmap : ∀ x : d.D, W (x : F) ∈ L.D)
    (hsurj : ∀ y : L.D, ∃ x : d.D, W (x : F) = (y : G))
    (hint : ∀ x : d.D, (L.hFull ⟨W (x : F), hmap x⟩ : G) = W ((d.hamiltonian x : F)))
    (hL : HasZeroDeficiencyOn L.D L.hFull) :
    HasZeroDeficiencyOn d.D d.hamiltonian := by sorry
