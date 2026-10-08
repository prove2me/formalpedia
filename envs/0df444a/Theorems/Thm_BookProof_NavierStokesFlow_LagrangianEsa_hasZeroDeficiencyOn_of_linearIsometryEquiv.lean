-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_hasZeroDeficiencyOn_of_linearIsometryEquiv
-- name    : BookProof.NavierStokesFlow.LagrangianEsa.hasZeroDeficiencyOn_of_linearIsometryEquiv
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T12:02:32.257185+00:00
-- url     : https://prove2.me/theorems/41551108-55a6-4953-ab72-c8cbc059fdcf
-- title:
--   `BookProof.NavierStokesFlow.LagrangianEsa.hasZeroDeficiencyOn_of_linearIsometryEquiv` (W : F ≃ₗᵢ[ℂ] G) {D : Submodule ℂ F} {D' : Submodule ℂ G} {H : D →ₗ[ℂ] D} {H' : D'...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesLagrangianEsa`.
--
--   `BookProof.NavierStokesFlow.LagrangianEsa.hasZeroDeficiencyOn_of_linearIsometryEquiv` (W : F ≃ₗᵢ[ℂ] G) {D : Submodule ℂ F} {D' : Submodule ℂ G} {H : D →ₗ[ℂ] D} {H' : D' →ₗ[ℂ] D'} (hmap : ∀ x : D, W (x : F) ∈ D') (hsurj : ∀ y : D', ∃ x : D, W (x : F) = (y : G)) (hint : ∀ x : D, (H' ⟨W (x : F), hmap x⟩ : G) = W ((H x : F))) (h : HasZeroDeficiencyOn D' H') : HasZeroDeficiencyOn D H
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.LagrangianEsa.hasZeroDeficiencyOn_of_linearIsometryEquiv`.

-- Generated from ChapterNavierStokesLagrangianEsa.lean — theorem BookProof.NavierStokesFlow.LagrangianEsa.hasZeroDeficiencyOn_of_linearIsometryEquiv
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa




open FullEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)
variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

theorem BookProof.NavierStokesFlow.LagrangianEsa.hasZeroDeficiencyOn_of_linearIsometryEquiv (W : F ≃ₗᵢ[ℂ] G) {D : Submodule ℂ F}
    {D' : Submodule ℂ G} {H : D →ₗ[ℂ] D} {H' : D' →ₗ[ℂ] D'}
    (hmap : ∀ x : D, W (x : F) ∈ D') (hsurj : ∀ y : D', ∃ x : D, W (x : F) = (y : G))
    (hint : ∀ x : D, (H' ⟨W (x : F), hmap x⟩ : G) = W ((H x : F)))
    (h : HasZeroDeficiencyOn D' H') : HasZeroDeficiencyOn D H := by sorry
